use super::*;

pub(super) fn c_expression_uses_variable(expression: &CExpression, variable: &str) -> bool {
    match expression {
        CExpression::Value(_) | CExpression::FunctionAddress(_) => false,
        CExpression::Variable(name) => name == variable,
        CExpression::Cast { expression, .. } => c_expression_uses_variable(expression, variable),
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_uses_variable(condition, variable)
                || c_expression_uses_variable(then_branch, variable)
                || c_expression_uses_variable(else_branch, variable)
        }
        CExpression::AddressOf(expression)
        | CExpression::Not(expression)
        | CExpression::BitwiseNot(expression)
        | CExpression::Load(expression)
        | CExpression::TypedLoad {
            pointer: expression,
            ..
        }
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        } => c_expression_uses_variable(expression, variable),
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
        | CExpression::BitwiseXor(left, right)
        | CExpression::Index(left, right) => {
            c_expression_uses_variable(left, variable)
                || c_expression_uses_variable(right, variable)
        }
    }
}

pub(in crate::surface) fn contains_old_expression(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::Old(_) => true,
        ContractExpression::CFragment(_)
        | ContractExpression::CBinding(_)
        | ContractExpression::ResourceWildcard => false,
        ContractExpression::ResourceCount(resource) => match resource.as_ref() {
            ResourceClause::Declared { arguments, .. } => {
                arguments.iter().any(contains_old_expression)
            }
            _ => false,
        },
        ContractExpression::Field { base, .. } => contains_old_expression(base),
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

pub(in crate::surface) fn contains_resource_count(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::ResourceCount(_) => true,
        ContractExpression::CFragment(_)
        | ContractExpression::CBinding(_)
        | ContractExpression::ResourceWildcard => false,
        ContractExpression::Field { base, .. }
        | ContractExpression::Old(base)
        | ContractExpression::At {
            expression: base, ..
        }
        | ContractExpression::BitwiseNot(base) => contains_resource_count(base),
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
            contains_resource_count(left) || contains_resource_count(right)
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            proposition_contains_resource_count(condition)
                || contains_resource_count(then_branch)
                || contains_resource_count(else_branch)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            contains_resource_count(start)
                || contains_resource_count(end)
                || contains_resource_count(initial)
                || contains_resource_count(body)
        }
        ContractExpression::Let { value, body, .. } => {
            contains_resource_count(value) || contains_resource_count(body)
        }
        ContractExpression::Call { arguments, .. } => arguments.iter().any(contains_resource_count),
    }
}

pub(in crate::surface) fn proposition_contains_resource_count(
    proposition: &ClickProposition,
) -> bool {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            contains_resource_count(left) || contains_resource_count(right)
        }
        ClickProposition::Defined { expression } => contains_resource_count(expression),
        ClickProposition::At { proposition, .. }
        | ClickProposition::Not(proposition)
        | ClickProposition::ForAll {
            body: proposition, ..
        }
        | ClickProposition::Exists {
            body: proposition, ..
        } => proposition_contains_resource_count(proposition),
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            proposition_contains_resource_count(left) || proposition_contains_resource_count(right)
        }
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            contains_resource_count(start)
                || contains_resource_count(end)
                || proposition_contains_resource_count(body)
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            arguments.iter().any(contains_resource_count)
        }
        ClickProposition::Separate { .. }
        | ClickProposition::Contains { .. }
        | ClickProposition::Loadable { .. } => false,
    }
}

pub(in crate::surface) fn collect_resource_count_families(
    proposition: &ClickProposition,
    families: &mut BTreeSet<String>,
) {
    fn collect_expression(expression: &ContractExpression, families: &mut BTreeSet<String>) {
        match expression {
            ContractExpression::ResourceCount(resource) => {
                if let ResourceClause::Declared {
                    name, arguments, ..
                } = resource.as_ref()
                {
                    families.insert(name.clone());
                    for argument in arguments {
                        collect_expression(argument, families);
                    }
                }
            }
            ContractExpression::Field { base, .. }
            | ContractExpression::Old(base)
            | ContractExpression::At {
                expression: base, ..
            }
            | ContractExpression::BitwiseNot(base) => collect_expression(base, families),
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
                collect_expression(left, families);
                collect_expression(right, families);
            }
            ContractExpression::If {
                condition,
                then_branch,
                else_branch,
            } => {
                collect_resource_count_families(condition, families);
                collect_expression(then_branch, families);
                collect_expression(else_branch, families);
            }
            ContractExpression::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            } => {
                collect_expression(start, families);
                collect_expression(end, families);
                collect_expression(initial, families);
                collect_expression(body, families);
            }
            ContractExpression::Let { value, body, .. } => {
                collect_expression(value, families);
                collect_expression(body, families);
            }
            ContractExpression::Call { arguments, .. } => {
                for argument in arguments {
                    collect_expression(argument, families);
                }
            }
            ContractExpression::CFragment(_)
            | ContractExpression::CBinding(_)
            | ContractExpression::ResourceWildcard => {}
        }
    }

    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            collect_expression(left, families);
            collect_expression(right, families);
        }
        ClickProposition::Defined { expression } => collect_expression(expression, families),
        ClickProposition::At { proposition, .. }
        | ClickProposition::Not(proposition)
        | ClickProposition::ForAll {
            body: proposition, ..
        }
        | ClickProposition::Exists {
            body: proposition, ..
        } => {
            collect_resource_count_families(proposition, families);
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            collect_resource_count_families(left, families);
            collect_resource_count_families(right, families);
        }
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            collect_expression(start, families);
            collect_expression(end, families);
            collect_resource_count_families(body, families);
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                collect_expression(argument, families);
            }
        }
        ClickProposition::Separate { .. }
        | ClickProposition::Contains { .. }
        | ClickProposition::Loadable { .. } => {}
    }
}

pub(in crate::surface) fn collect_called_predicates(
    proposition: &ClickProposition,
    names: &mut BTreeSet<String>,
) {
    match proposition {
        ClickProposition::PredicateCall { name, .. } => {
            names.insert(name.clone());
        }
        ClickProposition::At { proposition, .. }
        | ClickProposition::Not(proposition)
        | ClickProposition::ForAll {
            body: proposition, ..
        }
        | ClickProposition::Exists {
            body: proposition, ..
        } => {
            collect_called_predicates(proposition, names);
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            collect_called_predicates(left, names);
            collect_called_predicates(right, names);
        }
        ClickProposition::RangeAll { body, .. } | ClickProposition::RangeAny { body, .. } => {
            collect_called_predicates(body, names);
        }
        ClickProposition::Comparison { .. }
        | ClickProposition::Separate { .. }
        | ClickProposition::Contains { .. }
        | ClickProposition::Loadable { .. }
        | ClickProposition::Defined { .. } => {}
    }
}

fn contract_segment_contains_old_expression(segment: &ContractSegment) -> bool {
    [&segment.base, &segment.start, &segment.end]
        .into_iter()
        .any(|expression| {
            contains_old_expression(&ContractExpression::CFragment(expression.clone()))
        })
}

fn resource_subject_contains_old_expression(resource: &ResourceSubject) -> bool {
    match resource {
        ResourceSubject::Memory(segment) => contract_segment_contains_old_expression(segment),
        ResourceSubject::Declared { arguments, .. } => {
            arguments.iter().any(contains_old_expression)
        }
    }
}

pub(in crate::surface) fn proposition_contains_old_expression(
    proposition: &ClickProposition,
) -> bool {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            contains_old_expression(left) || contains_old_expression(right)
        }
        ClickProposition::Separate { left, right } => {
            resource_subject_contains_old_expression(left)
                || resource_subject_contains_old_expression(right)
        }
        ClickProposition::Contains { parent, child } => {
            resource_subject_contains_old_expression(parent)
                || resource_subject_contains_old_expression(child)
        }
        ClickProposition::Loadable { segment } => contract_segment_contains_old_expression(segment),
        ClickProposition::Defined { expression } => contains_old_expression(expression),
        ClickProposition::At { proposition, .. } => {
            proposition_contains_old_expression(proposition)
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

pub(in crate::surface) fn contains_at_expression(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::At { .. } => true,
        ContractExpression::CFragment(_)
        | ContractExpression::CBinding(_)
        | ContractExpression::ResourceWildcard => false,
        ContractExpression::ResourceCount(resource) => match resource.as_ref() {
            ResourceClause::Declared { arguments, .. } => {
                arguments.iter().any(contains_at_expression)
            }
            _ => false,
        },
        ContractExpression::Field { base, .. } => contains_at_expression(base),
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

fn resource_subject_contains_at_expression(resource: &ResourceSubject) -> bool {
    match resource {
        ResourceSubject::Memory(segment) => contract_segment_contains_at_expression(segment),
        ResourceSubject::Declared { arguments, .. } => arguments.iter().any(contains_at_expression),
    }
}

pub(in crate::surface) fn proposition_contains_at_expression(
    proposition: &ClickProposition,
) -> bool {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            contains_at_expression(left) || contains_at_expression(right)
        }
        ClickProposition::Separate { left, right } => {
            resource_subject_contains_at_expression(left)
                || resource_subject_contains_at_expression(right)
        }
        ClickProposition::Contains { parent, child } => {
            resource_subject_contains_at_expression(parent)
                || resource_subject_contains_at_expression(child)
        }
        ClickProposition::Loadable { segment } => contract_segment_contains_at_expression(segment),
        ClickProposition::Defined { expression } => contains_at_expression(expression),
        ClickProposition::At { .. } => true,
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

pub(in crate::surface) fn collect_click_function_calls(
    expression: &ContractExpression,
    calls: &mut BTreeSet<String>,
) {
    match expression {
        ContractExpression::CFragment(_)
        | ContractExpression::CBinding(_)
        | ContractExpression::ResourceWildcard => {}
        ContractExpression::ResourceCount(resource) => {
            if let ResourceClause::Declared { arguments, .. } = resource.as_ref() {
                for argument in arguments {
                    collect_click_function_calls(argument, calls);
                }
            }
        }
        ContractExpression::Field { base, .. } => collect_click_function_calls(base, calls),
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

fn collect_click_function_calls_in_resource_subject(
    resource: &ResourceSubject,
    calls: &mut BTreeSet<String>,
) {
    match resource {
        ResourceSubject::Memory(segment) => collect_click_function_calls_in_segment(segment, calls),
        ResourceSubject::Declared { arguments, .. } => {
            for argument in arguments {
                collect_click_function_calls(argument, calls);
            }
        }
    }
}

pub(in crate::surface) fn collect_click_function_calls_in_proposition(
    proposition: &ClickProposition,
    calls: &mut BTreeSet<String>,
) {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            collect_click_function_calls(left, calls);
            collect_click_function_calls(right, calls);
        }
        ClickProposition::Separate { left, right } => {
            collect_click_function_calls_in_resource_subject(left, calls);
            collect_click_function_calls_in_resource_subject(right, calls);
        }
        ClickProposition::Contains { parent, child } => {
            collect_click_function_calls_in_resource_subject(parent, calls);
            collect_click_function_calls_in_resource_subject(child, calls);
        }
        ClickProposition::Loadable { segment } => {
            collect_click_function_calls_in_segment(segment, calls);
        }
        ClickProposition::Defined { expression } => {
            collect_click_function_calls(expression, calls);
        }
        ClickProposition::At { proposition, .. } => {
            collect_click_function_calls_in_proposition(proposition, calls);
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

pub(super) fn validate_well_founded_click_recursion(
    definitions: &[ClickFunctionDefinition],
    function_calls: &BTreeMap<String, BTreeSet<String>>,
) -> Result<(), ClickError> {
    let definitions = definitions
        .iter()
        .map(|definition| (definition.name(), definition))
        .collect::<BTreeMap<_, _>>();
    let recursive_functions = definitions
        .keys()
        .filter(|name| {
            function_calls.get(**name).is_some_and(|callees| {
                callees.iter().any(|callee| {
                    callee == **name
                        || click_function_reaches(
                            callee,
                            name,
                            function_calls,
                            &mut BTreeSet::new(),
                        )
                })
            })
        })
        .copied()
        .collect::<BTreeSet<_>>();

    let mut measures = BTreeMap::new();
    for (name, definition) in &definitions {
        let measure = click_function_decreases_parameter(definition)?;
        if recursive_functions.contains(name) && measure.is_none() {
            return Err(ClickError::new(format!(
                "recursive pure function `{name}` requires `decreases <int32 parameter>`"
            )));
        }
        if recursive_functions.contains(name)
            && (definition.return_type() != C0Type::Int32
                || definition
                    .parameters()
                    .iter()
                    .any(|parameter| parameter.c_type() != C0Type::Int32))
        {
            return Err(ClickError::new(format!(
                "recursive pure function `{name}` currently supports only int32 parameters and an int32 result"
            )));
        }
        if let Some(measure) = measure {
            measures.insert((*name).to_string(), measure.to_string());
        }
    }

    for caller in &recursive_functions {
        validate_recursive_calls_in_expression(
            caller,
            definitions[caller].body(),
            &BTreeMap::new(),
            &definitions,
            function_calls,
            &measures,
        )?;
    }
    Ok(())
}

fn click_function_reaches(
    from: &str,
    target: &str,
    function_calls: &BTreeMap<String, BTreeSet<String>>,
    visited: &mut BTreeSet<String>,
) -> bool {
    if !visited.insert(from.to_string()) {
        return false;
    }
    function_calls.get(from).is_some_and(|callees| {
        callees.iter().any(|callee| {
            callee == target || click_function_reaches(callee, target, function_calls, visited)
        })
    })
}

fn click_function_decreases_parameter(
    definition: &ClickFunctionDefinition,
) -> Result<Option<&str>, ClickError> {
    let Some(measure) = definition.decreases() else {
        return Ok(None);
    };
    let Some(name) = contract_expression_variable(measure) else {
        return Err(ClickError::new(format!(
            "function `{}` currently requires `decreases` to name one int32 parameter",
            definition.name()
        )));
    };
    let Some(parameter) = definition
        .parameters()
        .iter()
        .find(|parameter| parameter.name() == name)
    else {
        return Err(ClickError::new(format!(
            "function `{}` decreases measure `{name}` is not a parameter",
            definition.name()
        )));
    };
    if parameter.c_type() != C0Type::Int32 {
        return Err(ClickError::new(format!(
            "function `{}` decreases measure `{name}` must be int32",
            definition.name()
        )));
    }
    Ok(Some(name))
}

fn contract_expression_variable(expression: &ContractExpression) -> Option<&str> {
    match expression {
        ContractExpression::CFragment(CExpression::Variable(name))
        | ContractExpression::CBinding(name) => Some(name),
        _ => None,
    }
}

fn contract_expression_int32_constant(expression: &ContractExpression) -> Option<i64> {
    let ContractExpression::CFragment(CExpression::Value(CValue::Int32(
        Bitvector32Term::Constant(value),
    ))) = expression
    else {
        return None;
    };
    Some(i64::from(*value as i32))
}

fn component_internal_call(
    caller: &str,
    callee: &str,
    function_calls: &BTreeMap<String, BTreeSet<String>>,
) -> bool {
    caller == callee || click_function_reaches(callee, caller, function_calls, &mut BTreeSet::new())
}

fn validate_recursive_call_edge(
    caller: &str,
    callee: &str,
    arguments: &[ContractExpression],
    lower_bounds: &BTreeMap<String, i64>,
    definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    function_calls: &BTreeMap<String, BTreeSet<String>>,
    measures: &BTreeMap<String, String>,
) -> Result<(), ClickError> {
    if !component_internal_call(caller, callee, function_calls) {
        return Ok(());
    }
    let caller_measure = measures
        .get(caller)
        .expect("recursive callers have validated measures");
    let callee_measure = measures.get(callee).ok_or_else(|| {
        ClickError::new(format!(
            "recursive call `{caller}` -> `{callee}` requires `{callee}` to declare `decreases`"
        ))
    })?;
    let measure_index = definitions
        .get(callee)
        .and_then(|definition| {
            definition
                .parameters()
                .iter()
                .position(|parameter| parameter.name() == callee_measure)
        })
        .ok_or_else(|| {
            ClickError::new(format!(
                "internal error locating decreases parameter `{callee_measure}` for `{callee}`"
            ))
        })?;
    let next = arguments.get(measure_index).ok_or_else(|| {
        ClickError::new(format!(
            "recursive call `{caller}` -> `{callee}` is missing its decreases argument"
        ))
    })?;
    let caller_lower = lower_bounds.get(caller_measure).copied();
    let valid = match next {
        ContractExpression::Subtract(left, right)
            if contract_expression_variable(left).is_some_and(|name| name == caller_measure) =>
        {
            let step = contract_expression_int32_constant(right);
            step.is_some_and(|step| step > 0 && caller_lower.is_some_and(|lower| lower >= step))
        }
        _ => contract_expression_int32_constant(next)
            .is_some_and(|next| next >= 0 && caller_lower.is_some_and(|lower| lower > next)),
    };
    if !valid {
        return Err(ClickError::new(format!(
            "recursive call `{caller}` -> `{callee}` must pass a nonnegative decreases measure strictly smaller than `{caller_measure}` on this path"
        )));
    }
    Ok(())
}

fn validate_recursive_calls_in_expression(
    caller: &str,
    expression: &ContractExpression,
    lower_bounds: &BTreeMap<String, i64>,
    definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    function_calls: &BTreeMap<String, BTreeSet<String>>,
    measures: &BTreeMap<String, String>,
) -> Result<(), ClickError> {
    let recurse = |expression: &ContractExpression, bounds: &BTreeMap<String, i64>| {
        validate_recursive_calls_in_expression(
            caller,
            expression,
            bounds,
            definitions,
            function_calls,
            measures,
        )
    };
    match expression {
        ContractExpression::CFragment(_)
        | ContractExpression::CBinding(_)
        | ContractExpression::ResourceWildcard => Ok(()),
        ContractExpression::ResourceCount(resource) => {
            if let ResourceClause::Declared { arguments, .. } = resource.as_ref() {
                for argument in arguments {
                    recurse(argument, lower_bounds)?;
                }
            }
            Ok(())
        }
        ContractExpression::Field { base, .. } => recurse(base, lower_bounds),
        ContractExpression::Old(body) | ContractExpression::BitwiseNot(body) => {
            recurse(body, lower_bounds)
        }
        ContractExpression::At { expression, .. } => recurse(expression, lower_bounds),
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
            recurse(left, lower_bounds)?;
            recurse(right, lower_bounds)
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            validate_recursive_calls_in_proposition(
                caller,
                condition,
                lower_bounds,
                definitions,
                function_calls,
                measures,
            )?;
            let mut then_bounds = lower_bounds.clone();
            add_condition_lower_bounds(condition, true, &mut then_bounds);
            let mut else_bounds = lower_bounds.clone();
            add_condition_lower_bounds(condition, false, &mut else_bounds);
            recurse(then_branch, &then_bounds)?;
            recurse(else_branch, &else_bounds)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            recurse(start, lower_bounds)?;
            recurse(end, lower_bounds)?;
            recurse(initial, lower_bounds)?;
            recurse(body, lower_bounds)
        }
        ContractExpression::Let { value, body, .. } => {
            recurse(value, lower_bounds)?;
            recurse(body, lower_bounds)
        }
        ContractExpression::Call { name, arguments } => {
            for argument in arguments {
                recurse(argument, lower_bounds)?;
            }
            validate_recursive_call_edge(
                caller,
                name,
                arguments,
                lower_bounds,
                definitions,
                function_calls,
                measures,
            )
        }
    }
}

fn validate_recursive_calls_in_proposition(
    caller: &str,
    proposition: &ClickProposition,
    lower_bounds: &BTreeMap<String, i64>,
    definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    function_calls: &BTreeMap<String, BTreeSet<String>>,
    measures: &BTreeMap<String, String>,
) -> Result<(), ClickError> {
    let expression = |expression: &ContractExpression| {
        validate_recursive_calls_in_expression(
            caller,
            expression,
            lower_bounds,
            definitions,
            function_calls,
            measures,
        )
    };
    let recurse_proposition = |proposition: &ClickProposition| {
        validate_recursive_calls_in_proposition(
            caller,
            proposition,
            lower_bounds,
            definitions,
            function_calls,
            measures,
        )
    };
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            expression(left)?;
            expression(right)
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            recurse_proposition(left)?;
            recurse_proposition(right)
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. }
        | ClickProposition::At {
            proposition: body, ..
        } => recurse_proposition(body),
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            expression(start)?;
            expression(end)?;
            recurse_proposition(body)
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                expression(argument)?;
            }
            Ok(())
        }
        ClickProposition::Defined { expression: body } => expression(body),
        ClickProposition::Separate { left, right }
        | ClickProposition::Contains {
            parent: left,
            child: right,
        } => {
            validate_recursive_calls_in_resource_subject(
                caller,
                left,
                lower_bounds,
                definitions,
                function_calls,
                measures,
            )?;
            validate_recursive_calls_in_resource_subject(
                caller,
                right,
                lower_bounds,
                definitions,
                function_calls,
                measures,
            )
        }
        ClickProposition::Loadable { segment } => validate_recursive_calls_in_segment(
            caller,
            segment,
            lower_bounds,
            definitions,
            function_calls,
            measures,
        ),
    }
}

fn validate_recursive_calls_in_resource_subject(
    caller: &str,
    subject: &ResourceSubject,
    lower_bounds: &BTreeMap<String, i64>,
    definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    function_calls: &BTreeMap<String, BTreeSet<String>>,
    measures: &BTreeMap<String, String>,
) -> Result<(), ClickError> {
    match subject {
        ResourceSubject::Memory(segment) => validate_recursive_calls_in_segment(
            caller,
            segment,
            lower_bounds,
            definitions,
            function_calls,
            measures,
        ),
        ResourceSubject::Declared { arguments, .. } => {
            for argument in arguments {
                validate_recursive_calls_in_expression(
                    caller,
                    argument,
                    lower_bounds,
                    definitions,
                    function_calls,
                    measures,
                )?;
            }
            Ok(())
        }
    }
}

fn validate_recursive_calls_in_segment(
    caller: &str,
    segment: &ContractSegment,
    lower_bounds: &BTreeMap<String, i64>,
    definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    function_calls: &BTreeMap<String, BTreeSet<String>>,
    measures: &BTreeMap<String, String>,
) -> Result<(), ClickError> {
    let expressions = match &segment.surface {
        ContractSegmentSurface::Range { base, start, end } => vec![base, start, end],
        ContractSegmentSurface::Field { .. } | ContractSegmentSurface::Object(_) => Vec::new(),
    };
    for expression in expressions {
        validate_recursive_calls_in_expression(
            caller,
            expression,
            lower_bounds,
            definitions,
            function_calls,
            measures,
        )?;
    }
    Ok(())
}

fn add_condition_lower_bounds(
    proposition: &ClickProposition,
    truth: bool,
    lower_bounds: &mut BTreeMap<String, i64>,
) {
    match proposition {
        ClickProposition::Not(body) => add_condition_lower_bounds(body, !truth, lower_bounds),
        ClickProposition::And(left, right) if truth => {
            add_condition_lower_bounds(left, true, lower_bounds);
            add_condition_lower_bounds(right, true, lower_bounds);
        }
        ClickProposition::Or(left, right) if !truth => {
            add_condition_lower_bounds(left, false, lower_bounds);
            add_condition_lower_bounds(right, false, lower_bounds);
        }
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let (name, operator, constant) = if let (Some(name), Some(constant)) = (
                contract_expression_variable(left),
                contract_expression_int32_constant(right),
            ) {
                (name, *operator, constant)
            } else if let (Some(constant), Some(name)) = (
                contract_expression_int32_constant(left),
                contract_expression_variable(right),
            ) {
                let reversed = match operator {
                    ComparisonOperator::LessThan => ComparisonOperator::GreaterThan,
                    ComparisonOperator::LessEqual => ComparisonOperator::GreaterEqual,
                    ComparisonOperator::GreaterThan => ComparisonOperator::LessThan,
                    ComparisonOperator::GreaterEqual => ComparisonOperator::LessEqual,
                    operator => *operator,
                };
                (name, reversed, constant)
            } else {
                return;
            };
            let bound = match (operator, truth) {
                (ComparisonOperator::GreaterEqual, true)
                | (ComparisonOperator::LessThan, false) => Some(constant),
                (ComparisonOperator::GreaterThan, true)
                | (ComparisonOperator::LessEqual, false) => constant.checked_add(1),
                (ComparisonOperator::Equal, true) | (ComparisonOperator::NotEqual, false) => {
                    Some(constant)
                }
                _ => None,
            };
            if let Some(bound) = bound {
                lower_bounds
                    .entry(name.to_string())
                    .and_modify(|current| *current = (*current).max(bound))
                    .or_insert(bound);
            }
        }
        _ => {}
    }
}
