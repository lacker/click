use super::prelude::*;

fn error(message: impl Into<String>) -> CTerminationError {
    CTerminationError {
        message: message.into(),
    }
}

fn int32_literal(expression: &CExpression) -> Option<i64> {
    let CExpression::Value(CValue::Int32(value)) = expression else {
        return None;
    };
    Some(value.as_const()? as i32 as i64)
}

fn variable_minus_positive(expression: &CExpression, variable: &str) -> Option<i64> {
    let CExpression::Subtract(left, right) = expression else {
        return None;
    };
    if left.as_ref() != &CExpression::Variable(variable.to_string()) {
        return None;
    }
    int32_literal(right).filter(|step| *step > 0)
}

fn substitute_c_expression_variables(
    expression: &CExpression,
    substitutions: &BTreeMap<String, CExpression>,
) -> CExpression {
    use CExpression::*;
    let unary =
        |body: &CExpression| Box::new(substitute_c_expression_variables(body, substitutions));
    let binary = |left: &CExpression, right: &CExpression| {
        (
            Box::new(substitute_c_expression_variables(left, substitutions)),
            Box::new(substitute_c_expression_variables(right, substitutions)),
        )
    };
    match expression {
        Value(_) | FunctionAddress(_) => expression.clone(),
        Cast {
            expression: body,
            target_type,
        } => Cast {
            expression: unary(body),
            target_type: *target_type,
        },
        Conditional {
            condition,
            then_branch,
            else_branch,
        } => Conditional {
            condition: unary(condition),
            then_branch: unary(then_branch),
            else_branch: unary(else_branch),
        },
        Variable(name) => substitutions
            .get(name)
            .cloned()
            .unwrap_or_else(|| expression.clone()),
        AddressOf(body) => AddressOf(unary(body)),
        PointerOffsetBytes { pointer, bytes } => PointerOffsetBytes {
            pointer: unary(pointer),
            bytes: *bytes,
        },
        LessThan(left, right) => {
            let (left, right) = binary(left, right);
            LessThan(left, right)
        }
        LessEqual(left, right) => {
            let (left, right) = binary(left, right);
            LessEqual(left, right)
        }
        GreaterThan(left, right) => {
            let (left, right) = binary(left, right);
            GreaterThan(left, right)
        }
        GreaterEqual(left, right) => {
            let (left, right) = binary(left, right);
            GreaterEqual(left, right)
        }
        Equal(left, right) => {
            let (left, right) = binary(left, right);
            Equal(left, right)
        }
        NotEqual(left, right) => {
            let (left, right) = binary(left, right);
            NotEqual(left, right)
        }
        Not(body) => Not(unary(body)),
        And(left, right) => {
            let (left, right) = binary(left, right);
            And(left, right)
        }
        Or(left, right) => {
            let (left, right) = binary(left, right);
            Or(left, right)
        }
        Add(left, right) => {
            let (left, right) = binary(left, right);
            Add(left, right)
        }
        Subtract(left, right) => {
            let (left, right) = binary(left, right);
            Subtract(left, right)
        }
        Multiply(left, right) => {
            let (left, right) = binary(left, right);
            Multiply(left, right)
        }
        Divide(left, right) => {
            let (left, right) = binary(left, right);
            Divide(left, right)
        }
        Remainder(left, right) => {
            let (left, right) = binary(left, right);
            Remainder(left, right)
        }
        ShiftLeft(left, right) => {
            let (left, right) = binary(left, right);
            ShiftLeft(left, right)
        }
        ShiftRight(left, right) => {
            let (left, right) = binary(left, right);
            ShiftRight(left, right)
        }
        BitwiseAnd(left, right) => {
            let (left, right) = binary(left, right);
            BitwiseAnd(left, right)
        }
        BitwiseOr(left, right) => {
            let (left, right) = binary(left, right);
            BitwiseOr(left, right)
        }
        BitwiseXor(left, right) => {
            let (left, right) = binary(left, right);
            BitwiseXor(left, right)
        }
        BitwiseNot(body) => BitwiseNot(unary(body)),
        Load(body) => Load(unary(body)),
        TypedLoad {
            pointer,
            value_type,
        } => TypedLoad {
            pointer: unary(pointer),
            value_type: *value_type,
        },
        Index(left, right) => {
            let (left, right) = binary(left, right);
            Index(left, right)
        }
    }
}

fn resolve_c_expression_aliases(
    expression: &CExpression,
    aliases: &BTreeMap<String, CExpression>,
) -> CExpression {
    let mut resolved = expression.clone();
    for _ in 0..=aliases.len() {
        let next = substitute_c_expression_variables(&resolved, aliases);
        if next == resolved {
            break;
        }
        resolved = next;
    }
    resolved
}

fn instantiate_structural_guard(
    proposition: &SpecProposition,
    substitutions: &BTreeMap<String, CExpression>,
) -> Option<SpecProposition> {
    let SpecProposition::Comparison {
        left,
        operator,
        right,
    } = proposition
    else {
        return None;
    };
    let instantiate = |expression: &SpecExpression| match expression {
        SpecExpression::Value(value) => Some(SpecExpression::Value(value.clone())),
        SpecExpression::CExpression(expression) => Some(SpecExpression::CExpression(
            substitute_c_expression_variables(expression, substitutions),
        )),
        _ => None,
    };
    Some(SpecProposition::Comparison {
        left: instantiate(left)?,
        operator: *operator,
        right: instantiate(right)?,
    })
}

#[derive(Clone)]
struct StructuralRecursionPath {
    aliases: BTreeMap<String, CExpression>,
    conditions: Vec<(CExpression, bool)>,
}

struct StructuralResourceMeasure {
    arguments: Vec<CExpression>,
    children: Vec<Vec<CExpression>>,
    guard: CExpression,
    guard_is_precondition: bool,
}

fn structural_guard_expression(proposition: &SpecProposition) -> Option<CExpression> {
    let SpecProposition::Comparison {
        left,
        operator,
        right,
    } = proposition
    else {
        return None;
    };
    let expression = |expression: &SpecExpression| match expression {
        SpecExpression::Value(value) => Some(CExpression::Value(value.clone())),
        SpecExpression::CExpression(expression) => Some(expression.clone()),
        _ => None,
    };
    let left = Box::new(expression(left)?);
    let right = Box::new(expression(right)?);
    Some(match operator {
        CComparisonOperator::Equal => CExpression::Equal(left, right),
        CComparisonOperator::NotEqual => CExpression::NotEqual(left, right),
        CComparisonOperator::LessThan => CExpression::LessThan(left, right),
        CComparisonOperator::LessEqual => CExpression::LessEqual(left, right),
        CComparisonOperator::GreaterThan => CExpression::GreaterThan(left, right),
        CComparisonOperator::GreaterEqual => CExpression::GreaterEqual(left, right),
    })
}

fn branch_establishes_structural_guard(
    branch_condition: &CExpression,
    branch_value: bool,
    guard: &CExpression,
) -> bool {
    #[derive(Eq, PartialEq)]
    enum ConditionAtom {
        Equal(CExpression, CExpression),
        LessThan(CExpression, CExpression),
    }

    fn normalized(expression: &CExpression, value: bool) -> (ConditionAtom, bool) {
        let ordered = |left: &CExpression, right: &CExpression| {
            if left <= right {
                (left.clone(), right.clone())
            } else {
                (right.clone(), left.clone())
            }
        };
        match expression {
            CExpression::Not(body) => normalized(body, !value),
            CExpression::Equal(left, right) => {
                let (left, right) = ordered(left, right);
                (ConditionAtom::Equal(left, right), value)
            }
            CExpression::NotEqual(left, right) => {
                let (left, right) = ordered(left, right);
                (ConditionAtom::Equal(left, right), !value)
            }
            CExpression::LessThan(left, right) => (
                ConditionAtom::LessThan(left.as_ref().clone(), right.as_ref().clone()),
                value,
            ),
            CExpression::GreaterEqual(left, right) => (
                ConditionAtom::LessThan(left.as_ref().clone(), right.as_ref().clone()),
                !value,
            ),
            CExpression::GreaterThan(left, right) => (
                ConditionAtom::LessThan(right.as_ref().clone(), left.as_ref().clone()),
                value,
            ),
            CExpression::LessEqual(left, right) => (
                ConditionAtom::LessThan(right.as_ref().clone(), left.as_ref().clone()),
                !value,
            ),
            expression => {
                let (left, right) = ordered(
                    expression,
                    &CExpression::Value(CValue::Int32(Bitvector32Term::Constant(0))),
                );
                (ConditionAtom::Equal(left, right), !value)
            }
        }
    }

    normalized(branch_condition, branch_value) == normalized(guard, true)
}

fn check_structural_recursive_call(
    function_name: &str,
    arguments: &[CExpression],
    function: &CFunction,
    measure_arguments: &[CExpression],
    child_arguments: &[Vec<CExpression>],
    guard: &CExpression,
    path: &StructuralRecursionPath,
) -> Result<(), CTerminationError> {
    if function_name != function.name() {
        return Ok(());
    }
    if !path
        .conditions
        .iter()
        .any(|(condition, value)| branch_establishes_structural_guard(condition, *value, guard))
    {
        return Err(error(format!(
            "recursive call to `{function_name}` is reachable without establishing the active structural resource guard"
        )));
    }
    let parameter_substitutions = function
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| {
            (
                parameter.name().to_string(),
                resolve_c_expression_aliases(argument, &path.aliases),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let call_measure_arguments = measure_arguments
        .iter()
        .map(|argument| substitute_c_expression_variables(argument, &parameter_substitutions))
        .collect::<Vec<_>>();
    if !child_arguments.contains(&call_measure_arguments) {
        return Err(error(format!(
            "recursive call to `{function_name}` does not pass a direct contained child of its structural resource measure"
        )));
    }
    Ok(())
}

fn structural_recursion_paths(
    statement: &CStatement,
    function: &CFunction,
    measure_arguments: &[CExpression],
    child_arguments: &[Vec<CExpression>],
    guard: &CExpression,
    paths: Vec<StructuralRecursionPath>,
) -> Result<Vec<StructuralRecursionPath>, CTerminationError> {
    match statement {
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Assert { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::Update { .. } => Ok(paths),
        CStatement::ContinueWithStep { step } => structural_recursion_paths(
            step,
            function,
            measure_arguments,
            child_arguments,
            guard,
            paths,
        ),
        CStatement::Return(_) => Ok(Vec::new()),
        CStatement::Declare { name, .. } => Ok(paths
            .into_iter()
            .map(|mut path| {
                path.aliases.remove(name);
                path
            })
            .collect()),
        CStatement::DeclareAggregate { name, .. } => Ok(paths
            .into_iter()
            .map(|mut path| {
                path.aliases.remove(name);
                path
            })
            .collect()),
        CStatement::Assign { name, expression } => Ok(paths
            .into_iter()
            .map(|mut path| {
                let expression = resolve_c_expression_aliases(expression, &path.aliases);
                path.aliases.insert(name.clone(), expression);
                path
            })
            .collect()),
        CStatement::HeapAllocate { target, .. } => Ok(paths
            .into_iter()
            .map(|mut path| {
                path.aliases.remove(target);
                path
            })
            .collect()),
        CStatement::CallAssign {
            target,
            function_name,
            arguments,
        } => {
            let mut next_paths = Vec::new();
            for mut path in paths {
                check_structural_recursive_call(
                    function_name,
                    arguments,
                    function,
                    measure_arguments,
                    child_arguments,
                    guard,
                    &path,
                )?;
                path.aliases.remove(target);
                next_paths.push(path);
            }
            Ok(next_paths)
        }
        CStatement::Call {
            function_name,
            arguments,
        } => {
            for path in &paths {
                check_structural_recursive_call(
                    function_name,
                    arguments,
                    function,
                    measure_arguments,
                    child_arguments,
                    guard,
                    path,
                )?;
            }
            Ok(paths)
        }
        CStatement::Seq(first, second) => structural_recursion_paths(
            second,
            function,
            measure_arguments,
            child_arguments,
            guard,
            structural_recursion_paths(
                first,
                function,
                measure_arguments,
                child_arguments,
                guard,
                paths,
            )?,
        ),
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut then_paths = Vec::new();
            let mut else_paths = Vec::new();
            for path in paths {
                let condition = resolve_c_expression_aliases(condition, &path.aliases);
                let mut then_path = path.clone();
                then_path.conditions.push((condition.clone(), true));
                then_paths.push(then_path);
                let mut else_path = path;
                else_path.conditions.push((condition, false));
                else_paths.push(else_path);
            }
            let mut paths = structural_recursion_paths(
                then_branch,
                function,
                measure_arguments,
                child_arguments,
                guard,
                then_paths,
            )?;
            paths.extend(structural_recursion_paths(
                else_branch,
                function,
                measure_arguments,
                child_arguments,
                guard,
                else_paths,
            )?);
            Ok(paths)
        }
        CStatement::While { body, .. } => {
            let mut calls = BTreeSet::new();
            statement_calls(body, &mut calls);
            if calls.contains(function.name()) {
                return Err(error(
                    "recursive calls inside a loop require a lexicographic measure and are not yet supported",
                ));
            }
            Ok(paths)
        }
        CStatement::Switch { cases, .. } => {
            let incoming_paths = paths;
            let mut paths = Vec::new();
            for case in cases {
                paths.extend(structural_recursion_paths(
                    &case.body,
                    function,
                    measure_arguments,
                    child_arguments,
                    guard,
                    incoming_paths.clone(),
                )?);
            }
            Ok(paths)
        }
    }
}

fn structural_resource_children(
    function: &CFunction,
    requirement_index: usize,
) -> Result<StructuralResourceMeasure, CTerminationError> {
    let Some(CResourceSpec::Composite {
        name, arguments, ..
    }) = function.resource_requires().get(requirement_index)
    else {
        return Err(error(format!(
            "structural resource measure index is invalid for `{}`",
            function.name()
        )));
    };
    let definition = function
        .composite_resource_definitions()
        .iter()
        .find(|definition| definition.name() == name)
        .ok_or_else(|| error(format!("resource measure `{name}` has no definition")))?;
    if !definition.is_recursive() {
        return Err(error(format!(
            "resource measure `{name}` is not directly recursive"
        )));
    }
    if definition.parameters().len() != arguments.len() {
        return Err(error(format!(
            "resource measure `{name}` has mismatched definition arguments"
        )));
    }
    let substitutions = definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
        .collect::<BTreeMap<_, _>>();
    let guard = definition
        .condition()
        .and_then(|condition| instantiate_structural_guard(condition, &substitutions))
        .ok_or_else(|| {
            error(format!(
                "resource measure `{name}` currently requires a simple comparison guard"
            ))
        })?;
    let guard_is_precondition = function.contract_requires().contains(&guard);
    let guard = structural_guard_expression(&guard).ok_or_else(|| {
        error(format!(
            "resource measure `{name}` currently requires a simple comparison guard"
        ))
    })?;
    let children = definition
        .contains()
        .iter()
        .filter_map(|contained| match contained {
            CResourceSpec::Composite {
                name: child_name,
                arguments,
                ..
            } if child_name == name => Some(
                arguments
                    .iter()
                    .map(|argument| substitute_c_expression_variables(argument, &substitutions))
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        })
        .collect::<Vec<_>>();
    if children.is_empty() {
        return Err(error(format!(
            "resource measure `{name}` has no direct recursive child"
        )));
    }
    Ok(StructuralResourceMeasure {
        arguments: arguments.clone(),
        children,
        guard,
        guard_is_precondition,
    })
}

fn refined_lower_bound(condition: &CExpression, variable: &str, branch: bool, current: i64) -> i64 {
    use CExpression::*;
    let direct = match condition {
        GreaterThan(left, right) if left.as_ref() == &Variable(variable.to_string()) && branch => {
            int32_literal(right).map(|value| value + 1)
        }
        GreaterEqual(left, right) if left.as_ref() == &Variable(variable.to_string()) && branch => {
            int32_literal(right)
        }
        LessThan(left, right) if left.as_ref() == &Variable(variable.to_string()) && !branch => {
            int32_literal(right)
        }
        LessEqual(left, right) if left.as_ref() == &Variable(variable.to_string()) && !branch => {
            int32_literal(right).map(|value| value + 1)
        }
        LessThan(left, right) if right.as_ref() == &Variable(variable.to_string()) && branch => {
            int32_literal(left).map(|value| value + 1)
        }
        LessEqual(left, right) if right.as_ref() == &Variable(variable.to_string()) && branch => {
            int32_literal(left)
        }
        GreaterThan(left, right)
            if right.as_ref() == &Variable(variable.to_string()) && !branch =>
        {
            int32_literal(left)
        }
        GreaterEqual(left, right)
            if right.as_ref() == &Variable(variable.to_string()) && !branch =>
        {
            int32_literal(left).map(|value| value + 1)
        }
        And(left, right) if branch => Some(
            refined_lower_bound(left, variable, true, current)
                .max(refined_lower_bound(right, variable, true, current)),
        ),
        Or(left, right) if !branch => Some(
            refined_lower_bound(left, variable, false, current)
                .max(refined_lower_bound(right, variable, false, current)),
        ),
        Not(inner) => Some(refined_lower_bound(inner, variable, !branch, current)),
        _ => None,
    };
    direct.unwrap_or(current).max(current)
}

/// Whether `expression` takes the address of the local `name`.
fn expression_takes_address_of(expression: &CExpression, name: &str) -> bool {
    use CExpression::*;
    let inner = |body: &CExpression| expression_takes_address_of(body, name);
    match expression {
        Value(_) | Variable(_) | FunctionAddress(_) => false,
        Cast { expression, .. } => inner(expression),
        Conditional {
            condition,
            then_branch,
            else_branch,
        } => inner(condition) || inner(then_branch) || inner(else_branch),
        AddressOf(body) => {
            matches!(body.as_ref(), Variable(target) if target == name) || inner(body)
        }
        PointerOffsetBytes { pointer, .. } | TypedLoad { pointer, .. } => inner(pointer),
        Not(body) | BitwiseNot(body) | Load(body) => inner(body),
        LessThan(left, right)
        | LessEqual(left, right)
        | GreaterThan(left, right)
        | GreaterEqual(left, right)
        | Equal(left, right)
        | NotEqual(left, right)
        | And(left, right)
        | Or(left, right)
        | Add(left, right)
        | Subtract(left, right)
        | Multiply(left, right)
        | Divide(left, right)
        | Remainder(left, right)
        | ShiftLeft(left, right)
        | ShiftRight(left, right)
        | BitwiseAnd(left, right)
        | BitwiseOr(left, right)
        | BitwiseXor(left, right)
        | Index(left, right) => inner(left) || inner(right),
    }
}

fn collect_c_expression_variables(expression: &CExpression, names: &mut BTreeSet<String>) {
    use CExpression::*;
    match expression {
        Variable(name) => {
            names.insert(name.clone());
        }
        Cast { expression, .. }
        | AddressOf(expression)
        | PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | Not(expression)
        | BitwiseNot(expression)
        | Load(expression) => collect_c_expression_variables(expression, names),
        Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_c_expression_variables(condition, names);
            collect_c_expression_variables(then_branch, names);
            collect_c_expression_variables(else_branch, names);
        }
        LessThan(left, right)
        | LessEqual(left, right)
        | GreaterThan(left, right)
        | GreaterEqual(left, right)
        | Equal(left, right)
        | NotEqual(left, right)
        | And(left, right)
        | Or(left, right)
        | Add(left, right)
        | Subtract(left, right)
        | Multiply(left, right)
        | Divide(left, right)
        | Remainder(left, right)
        | ShiftLeft(left, right)
        | ShiftRight(left, right)
        | BitwiseAnd(left, right)
        | BitwiseOr(left, right)
        | BitwiseXor(left, right)
        | Index(left, right) => {
            collect_c_expression_variables(left, names);
            collect_c_expression_variables(right, names);
        }
        TypedLoad { pointer, .. } => collect_c_expression_variables(pointer, names),
        Value(_) | FunctionAddress(_) => {}
    }
}

/// Whether any expression in `statement` takes the address of the local
/// `name`. A local's cell can be written through a pointer only if its
/// address was taken somewhere in the function, so this is the complete
/// syntactic condition for "a store or a callee might change this local
/// without assigning it by name".
fn statement_takes_address_of(statement: &CStatement, name: &str) -> bool {
    let escapes = |expression: &CExpression| expression_takes_address_of(expression, name);
    match statement {
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. } => false,
        CStatement::ContinueWithStep { step } => statement_takes_address_of(step, name),
        CStatement::Assign { expression, .. } | CStatement::Return(expression) => {
            escapes(expression)
        }
        CStatement::CallAssign { arguments, .. } | CStatement::Call { arguments, .. } => {
            arguments.iter().any(escapes)
        }
        CStatement::HeapAllocate { bytes, .. } => escapes(bytes),
        CStatement::HeapFree { pointer } => escapes(pointer),
        CStatement::Assert { condition, .. } => escapes(condition),
        CStatement::Store { pointer, value } | CStatement::TypedStore { pointer, value, .. } => {
            escapes(pointer) || escapes(value)
        }
        CStatement::Update {
            target, operand, ..
        } => escapes(target) || escapes(operand),
        CStatement::Seq(first, second) => {
            statement_takes_address_of(first, name) || statement_takes_address_of(second, name)
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            escapes(condition)
                || statement_takes_address_of(then_branch, name)
                || statement_takes_address_of(else_branch, name)
        }
        CStatement::While {
            condition, body, ..
        } => escapes(condition) || statement_takes_address_of(body, name),
        CStatement::Switch { expression, cases } => {
            escapes(expression)
                || cases
                    .iter()
                    .any(|case| statement_takes_address_of(&case.body, name))
        }
    }
}

/// The ranking checkers below are syntactic over assignments by name, so a
/// measure whose address escapes could be reset through a pointer, directly
/// or by a callee, without any ranked update. Such measures are rejected.
fn reject_address_escaped_measure(
    function_name: &str,
    measure: &str,
    body: &CStatement,
) -> Result<(), CTerminationError> {
    if statement_takes_address_of(body, measure) {
        return Err(error(format!(
            "termination measure `{measure}` in `{function_name}` has its address taken; a store \
             through that pointer could change the measure without a ranked update"
        )));
    }
    Ok(())
}

fn reject_address_escaped_expression_measure(
    function_name: &str,
    measure: &CExpression,
    body: &CStatement,
) -> Result<(), CTerminationError> {
    let mut variables = BTreeSet::new();
    collect_c_expression_variables(measure, &mut variables);
    for variable in variables {
        reject_address_escaped_measure(function_name, &variable, body)?;
    }
    Ok(())
}

fn statement_assigned_variables(statement: &CStatement, names: &mut BTreeSet<String>) {
    match statement {
        CStatement::Assign { name, .. }
        | CStatement::CallAssign { target: name, .. }
        | CStatement::HeapAllocate { target: name, .. } => {
            names.insert(name.clone());
        }
        CStatement::Update { target, .. } => {
            if let CExpression::Variable(name) = target {
                names.insert(name.clone());
            }
        }
        CStatement::Seq(first, second) => {
            statement_assigned_variables(first, names);
            statement_assigned_variables(second, names);
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            statement_assigned_variables(then_branch, names);
            statement_assigned_variables(else_branch, names);
        }
        CStatement::While { body, .. } => statement_assigned_variables(body, names),
        CStatement::Switch { cases, .. } => {
            for case in cases {
                statement_assigned_variables(&case.body, names);
            }
        }
        CStatement::ContinueWithStep { step } => statement_assigned_variables(step, names),
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Call { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. } => {}
    }
}

fn statement_calls(statement: &CStatement, calls: &mut BTreeSet<String>) {
    match statement {
        CStatement::CallAssign { function_name, .. } | CStatement::Call { function_name, .. } => {
            calls.insert(function_name.clone());
        }
        CStatement::Seq(first, second) => {
            statement_calls(first, calls);
            statement_calls(second, calls);
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            statement_calls(then_branch, calls);
            statement_calls(else_branch, calls);
        }
        CStatement::While { body, .. } => statement_calls(body, calls),
        CStatement::Switch {
            expression: _,
            cases,
        } => {
            for case in cases {
                statement_calls(&case.body, calls);
            }
        }
        CStatement::ContinueWithStep { step } => statement_calls(step, calls),
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assign { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::Update { .. } => {}
    }
}

fn recursion_paths(
    statement: &CStatement,
    measure: &str,
    component: &BTreeSet<String>,
    parameter_indices: &BTreeMap<String, usize>,
    lower_bounds: Vec<i64>,
) -> Result<Vec<i64>, CTerminationError> {
    match statement {
        CStatement::Skip
        | CStatement::Continue
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assert { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::Update { .. } => Ok(lower_bounds),
        CStatement::ContinueWithStep { step } => {
            recursion_paths(step, measure, component, parameter_indices, lower_bounds)
        }
        CStatement::Return(_) => Ok(Vec::new()),
        CStatement::Break => Ok(Vec::new()),
        CStatement::Assign { name, .. } if name == measure => Err(error(format!(
            "termination measure `{measure}` is reassigned; this first implementation requires an unchanged function parameter"
        ))),
        CStatement::Assign { .. } => Ok(lower_bounds),
        CStatement::HeapAllocate { target, .. } if target == measure => Err(error(format!(
            "recursive termination measure `{measure}` is overwritten by an allocation result"
        ))),
        CStatement::HeapAllocate { .. } => Ok(lower_bounds),
        CStatement::CallAssign {
            target,
            function_name,
            arguments,
        } => {
            if target == measure {
                return Err(error(format!(
                    "recursive termination measure `{measure}` is overwritten by a call result"
                )));
            }
            if component.contains(function_name) {
                let index = parameter_indices[function_name];
                let argument = arguments.get(index).ok_or_else(|| {
                    error(format!(
                        "recursive call to `{function_name}` has no argument for its termination measure"
                    ))
                })?;
                let step = variable_minus_positive(argument, measure).ok_or_else(|| {
                    error(format!(
                        "recursive call to `{function_name}` must pass `{measure} - K` for a positive constant K"
                    ))
                })?;
                if lower_bounds.iter().any(|bound| *bound < step) {
                    return Err(error(format!(
                        "recursive call to `{function_name}` does not establish that `{measure} - {step}` is nonnegative"
                    )));
                }
            }
            Ok(lower_bounds)
        }
        CStatement::Call {
            function_name,
            arguments,
        } => {
            if component.contains(function_name) {
                let index = parameter_indices[function_name];
                let argument = arguments.get(index).ok_or_else(|| {
                    error(format!(
                        "recursive call to `{function_name}` has no argument for its termination measure"
                    ))
                })?;
                let step = variable_minus_positive(argument, measure).ok_or_else(|| {
                    error(format!(
                        "recursive call to `{function_name}` must pass `{measure} - K` for a positive constant K"
                    ))
                })?;
                if lower_bounds.iter().any(|bound| *bound < step) {
                    return Err(error(format!(
                        "recursive call to `{function_name}` does not establish that `{measure} - {step}` is nonnegative"
                    )));
                }
            }
            Ok(lower_bounds)
        }
        CStatement::Seq(first, second) => recursion_paths(
            second,
            measure,
            component,
            parameter_indices,
            recursion_paths(first, measure, component, parameter_indices, lower_bounds)?,
        ),
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut paths = Vec::new();
            for lower_bound in lower_bounds {
                paths.extend(recursion_paths(
                    then_branch,
                    measure,
                    component,
                    parameter_indices,
                    vec![refined_lower_bound(condition, measure, true, lower_bound)],
                )?);
                paths.extend(recursion_paths(
                    else_branch,
                    measure,
                    component,
                    parameter_indices,
                    vec![refined_lower_bound(condition, measure, false, lower_bound)],
                )?);
            }
            Ok(paths)
        }
        CStatement::While { body, .. } => {
            let mut calls = BTreeSet::new();
            statement_calls(body, &mut calls);
            if calls.iter().any(|call| component.contains(call)) {
                return Err(error(
                    "recursive calls inside a loop require a lexicographic measure and are not yet supported",
                ));
            }
            Ok(lower_bounds)
        }
        CStatement::Switch { cases, .. } => {
            let mut paths = Vec::new();
            for case in cases {
                paths.extend(recursion_paths(
                    &case.body,
                    measure,
                    component,
                    parameter_indices,
                    lower_bounds.clone(),
                )?);
            }
            Ok(paths)
        }
    }
}

#[derive(Clone)]
struct LoopRankingPath {
    aliases: BTreeMap<String, CExpression>,
    conditions: Vec<(CExpression, bool)>,
}

fn updated_c_expression(
    current: CExpression,
    operator: CUpdateOperator,
    operand: CExpression,
) -> CExpression {
    let current = Box::new(current);
    let operand = Box::new(operand);
    match operator {
        CUpdateOperator::Add => CExpression::Add(current, operand),
        CUpdateOperator::Subtract => CExpression::Subtract(current, operand),
        CUpdateOperator::Multiply => CExpression::Multiply(current, operand),
        CUpdateOperator::Divide => CExpression::Divide(current, operand),
        CUpdateOperator::Remainder => CExpression::Remainder(current, operand),
        CUpdateOperator::ShiftLeft => CExpression::ShiftLeft(current, operand),
        CUpdateOperator::ShiftRight => CExpression::ShiftRight(current, operand),
        CUpdateOperator::BitwiseAnd => CExpression::BitwiseAnd(current, operand),
        CUpdateOperator::BitwiseOr => CExpression::BitwiseOr(current, operand),
        CUpdateOperator::BitwiseXor => CExpression::BitwiseXor(current, operand),
    }
}

fn loop_paths(
    statement: &CStatement,
    measure_variables: &BTreeSet<String>,
    paths: Vec<LoopRankingPath>,
) -> Result<Vec<LoopRankingPath>, CTerminationError> {
    match statement {
        CStatement::Skip
        | CStatement::Continue
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assert { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::Call { .. } => Ok(paths),
        CStatement::ContinueWithStep { step } => loop_paths(step, measure_variables, paths),
        CStatement::Return(_) | CStatement::Break => Ok(Vec::new()),
        CStatement::Declare { name, .. } => Ok(paths
            .into_iter()
            .map(|mut path| {
                path.aliases.remove(name);
                path
            })
            .collect()),
        CStatement::Assign { name, expression } => Ok(paths
            .into_iter()
            .map(|mut path| {
                let expression = substitute_c_expression_variables(expression, &path.aliases);
                path.aliases.insert(name.clone(), expression);
                path
            })
            .collect()),
        CStatement::Update {
            target,
            operator,
            operand,
        } => {
            let CExpression::Variable(name) = target else {
                return Ok(paths);
            };
            Ok(paths
                .into_iter()
                .map(|mut path| {
                    let current = path
                        .aliases
                        .get(name)
                        .cloned()
                        .unwrap_or_else(|| CExpression::Variable(name.clone()));
                    let operand = substitute_c_expression_variables(operand, &path.aliases);
                    path.aliases.insert(
                        name.clone(),
                        updated_c_expression(current, *operator, operand),
                    );
                    path
                })
                .collect())
        }
        CStatement::HeapAllocate { target, .. } => {
            if measure_variables.contains(target) {
                return Err(error(format!(
                    "loop termination measure variable `{target}` is overwritten by an allocation result"
                )));
            }
            Ok(paths
                .into_iter()
                .map(|mut path| {
                    path.aliases.remove(target);
                    path
                })
                .collect())
        }
        CStatement::CallAssign { target, .. } => {
            if measure_variables.contains(target) {
                return Err(error(format!(
                    "loop termination measure variable `{target}` is overwritten by a call result"
                )));
            }
            Ok(paths
                .into_iter()
                .map(|mut path| {
                    path.aliases.remove(target);
                    path
                })
                .collect())
        }
        CStatement::Seq(first, second) => loop_paths(
            second,
            measure_variables,
            loop_paths(first, measure_variables, paths)?,
        ),
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut then_paths = Vec::new();
            let mut else_paths = Vec::new();
            for path in paths {
                let condition = substitute_c_expression_variables(condition, &path.aliases);
                let mut then_path = path.clone();
                then_path.conditions.push((condition.clone(), true));
                then_paths.push(then_path);
                let mut else_path = path;
                else_path.conditions.push((condition, false));
                else_paths.push(else_path);
            }
            let mut paths = loop_paths(then_branch, measure_variables, then_paths)?;
            paths.extend(loop_paths(else_branch, measure_variables, else_paths)?);
            Ok(paths)
        }
        CStatement::While { body, .. } => {
            let mut nested_writes = BTreeSet::new();
            statement_assigned_variables(body, &mut nested_writes);
            let changed_measure_variables = nested_writes
                .intersection(measure_variables)
                .cloned()
                .collect::<BTreeSet<_>>();
            Ok(paths
                .into_iter()
                .map(|mut path| {
                    // An independently ranked inner loop is a terminating,
                    // invariant-preserving phase of the enclosing iteration.
                    // Its exact final values are intentionally not guessed:
                    // forget only aliases for variables that can affect the
                    // enclosing ranking, leaving the outer invariants to
                    // establish their post-loop well-foundedness.
                    for name in &changed_measure_variables {
                        path.aliases.remove(name);
                    }
                    path
                })
                .collect())
        }
        CStatement::Switch { cases, .. } => {
            let incoming = paths;
            let mut paths = Vec::new();
            for case in cases {
                paths.extend(loop_paths(&case.body, measure_variables, incoming.clone())?);
            }
            Ok(paths)
        }
    }
}

fn resolve_loop_c_expression_aliases(
    expression: &CExpression,
    aliases: &BTreeMap<String, CExpression>,
) -> CExpression {
    let mut resolved = expression.clone();
    let mut blocked = BTreeSet::new();
    let mut seen = BTreeSet::new();
    seen.insert(resolved.clone());
    for _ in 0..=aliases.len() {
        let substitutions = aliases
            .iter()
            .filter(|(name, _)| !blocked.contains(*name))
            .map(|(name, expression)| (name.clone(), expression.clone()))
            .collect::<BTreeMap<_, _>>();
        let next = substitute_c_expression_variables(&resolved, &substitutions);
        if next == resolved || !seen.insert(next.clone()) {
            break;
        }
        for (name, replacement) in aliases {
            let mut variables = BTreeSet::new();
            collect_c_expression_variables(replacement, &mut variables);
            if variables.contains(name) {
                blocked.insert(name.clone());
            }
        }
        resolved = next;
    }
    resolved
}

fn ranking_variable_map(names: &BTreeSet<String>) -> BTreeMap<String, Variable> {
    names
        .iter()
        .enumerate()
        .map(|(index, name)| (name.clone(), Variable(index as u64)))
        .collect()
}

fn ranking_term(
    expression: &CExpression,
    variables: &BTreeMap<String, Variable>,
) -> Result<Bitvector32Term, CTerminationError> {
    use CExpression::*;
    let binary = |left: &CExpression,
                  right: &CExpression,
                  operation: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term|
     -> Result<Bitvector32Term, CTerminationError> {
        Ok(operation(
            ranking_term(left, variables)?,
            ranking_term(right, variables)?,
        ))
    };
    match expression {
        Value(CValue::Int32(value)) | Value(CValue::UInt8(value)) => Ok(value.clone()),
        Value(_) => Err(error("termination measures must be int32 expressions")),
        Variable(name) => variables
            .get(name)
            .copied()
            .map(Bitvector32Term::Variable)
            .ok_or_else(|| {
                error(format!(
                    "termination measure references unknown variable `{name}`"
                ))
            }),
        Cast {
            expression,
            target_type: CType::Int32 | CType::UInt8,
        } => ranking_term(expression, variables),
        Cast { .. }
        | FunctionAddress(_)
        | AddressOf(_)
        | PointerOffsetBytes { .. }
        | Load(_)
        | TypedLoad { .. }
        | Index(_, _) => Err(error(
            "termination measures may only use scalar int32 expressions",
        )),
        Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            let (condition, value) = ranking_condition_term(condition, variables)?;
            let then_term = ranking_term(then_branch, variables)?;
            let else_term = ranking_term(else_branch, variables)?;
            let (then_term, else_term) = if value {
                (then_term, else_term)
            } else {
                (else_term, then_term)
            };
            Ok(Bitvector32Term::If {
                condition: Box::new(condition),
                then_term: Box::new(then_term),
                else_term: Box::new(else_term),
            })
        }
        Add(left, right) => binary(left, right, Bitvector32Term::add),
        Subtract(left, right) => binary(left, right, Bitvector32Term::subtract),
        Multiply(left, right) => binary(left, right, Bitvector32Term::multiply),
        Divide(left, right) => binary(left, right, Bitvector32Term::divide),
        Remainder(left, right) => binary(left, right, Bitvector32Term::remainder),
        ShiftLeft(left, right) => binary(left, right, Bitvector32Term::shift_left),
        ShiftRight(left, right) => binary(left, right, Bitvector32Term::arithmetic_shift_right),
        BitwiseAnd(left, right) => binary(left, right, Bitvector32Term::bitwise_and),
        BitwiseOr(left, right) => binary(left, right, Bitvector32Term::bitwise_or),
        BitwiseXor(left, right) => binary(left, right, Bitvector32Term::bitwise_xor),
        BitwiseNot(value) => Ok(Bitvector32Term::bitwise_not(ranking_term(
            value, variables,
        )?)),
        LessThan(_, _)
        | LessEqual(_, _)
        | GreaterThan(_, _)
        | GreaterEqual(_, _)
        | Equal(_, _)
        | NotEqual(_, _)
        | Not(_)
        | And(_, _)
        | Or(_, _) => Err(error("termination measures must have an int32 value")),
    }
}

fn ranking_condition_term(
    expression: &CExpression,
    variables: &BTreeMap<String, Variable>,
) -> Result<(ConditionTerm, bool), CTerminationError> {
    use CExpression::*;
    let binary = |left: &CExpression,
                  right: &CExpression,
                  operation: fn(Bitvector32Term, Bitvector32Term) -> ConditionTerm|
     -> Result<(ConditionTerm, bool), CTerminationError> {
        Ok((
            operation(
                ranking_term(left, variables)?,
                ranking_term(right, variables)?,
            ),
            true,
        ))
    };
    match expression {
        LessThan(left, right) => binary(left, right, ConditionTerm::signed_less_than),
        LessEqual(left, right) => binary(left, right, ConditionTerm::signed_less_equal),
        GreaterThan(left, right) => binary(left, right, ConditionTerm::signed_greater_than),
        GreaterEqual(left, right) => binary(left, right, ConditionTerm::signed_greater_equal),
        Equal(left, right) => binary(left, right, ConditionTerm::equal),
        NotEqual(left, right) => {
            let (condition, _) = binary(left, right, ConditionTerm::equal)?;
            Ok((condition, false))
        }
        Not(inner) => {
            let (condition, value) = ranking_condition_term(inner, variables)?;
            Ok((condition, !value))
        }
        And(_, _) | Or(_, _) => Err(error(
            "compound boolean conditions are not atomic ranking assumptions",
        )),
        _ => Ok((
            ConditionTerm::equal(
                ranking_term(expression, variables)?,
                Bitvector32Term::Constant(0),
            ),
            false,
        )),
    }
}

fn assume_ranking_condition(
    context: PureFactContext,
    expression: &CExpression,
    value: bool,
    variables: &BTreeMap<String, Variable>,
) -> Result<PureFactContext, CTerminationError> {
    match expression {
        CExpression::And(left, right) if value => Ok(assume_ranking_condition(
            assume_ranking_condition(context, left, true, variables)?,
            right,
            true,
            variables,
        )?),
        CExpression::Or(left, right) if !value => Ok(assume_ranking_condition(
            assume_ranking_condition(context, left, false, variables)?,
            right,
            false,
            variables,
        )?),
        CExpression::And(_, _) | CExpression::Or(_, _) => Ok(context),
        _ => {
            let (condition, condition_value) = ranking_condition_term(expression, variables)?;
            Ok(context.assume_condition(condition, value == condition_value))
        }
    }
}

fn termination_measure_display(measure: &CExpression) -> String {
    match measure {
        CExpression::Variable(name) => name.clone(),
        _ => format!("{measure:?}"),
    }
}

fn termination_measures_display(measures: &[CExpression]) -> String {
    let components = measures
        .iter()
        .map(termination_measure_display)
        .collect::<Vec<_>>();
    if components.len() == 1 {
        components[0].clone()
    } else {
        format!("({})", components.join(", "))
    }
}

fn spec_expression_to_c_expression(expression: &SpecExpression) -> Option<CExpression> {
    match expression {
        SpecExpression::Value(value) => Some(CExpression::Value(value.clone())),
        SpecExpression::CExpression(expression) => Some(expression.clone()),
        SpecExpression::Add(left, right) => Some(CExpression::Add(
            Box::new(spec_expression_to_c_expression(left)?),
            Box::new(spec_expression_to_c_expression(right)?),
        )),
        SpecExpression::Subtract(left, right) => Some(CExpression::Subtract(
            Box::new(spec_expression_to_c_expression(left)?),
            Box::new(spec_expression_to_c_expression(right)?),
        )),
        SpecExpression::Multiply(left, right) => Some(CExpression::Multiply(
            Box::new(spec_expression_to_c_expression(left)?),
            Box::new(spec_expression_to_c_expression(right)?),
        )),
        SpecExpression::Divide(left, right) => Some(CExpression::Divide(
            Box::new(spec_expression_to_c_expression(left)?),
            Box::new(spec_expression_to_c_expression(right)?),
        )),
        SpecExpression::Remainder(left, right) => Some(CExpression::Remainder(
            Box::new(spec_expression_to_c_expression(left)?),
            Box::new(spec_expression_to_c_expression(right)?),
        )),
        SpecExpression::ShiftLeft(left, right) => Some(CExpression::ShiftLeft(
            Box::new(spec_expression_to_c_expression(left)?),
            Box::new(spec_expression_to_c_expression(right)?),
        )),
        SpecExpression::ShiftRight(left, right) => Some(CExpression::ShiftRight(
            Box::new(spec_expression_to_c_expression(left)?),
            Box::new(spec_expression_to_c_expression(right)?),
        )),
        SpecExpression::BitwiseAnd(left, right) => Some(CExpression::BitwiseAnd(
            Box::new(spec_expression_to_c_expression(left)?),
            Box::new(spec_expression_to_c_expression(right)?),
        )),
        SpecExpression::BitwiseOr(left, right) => Some(CExpression::BitwiseOr(
            Box::new(spec_expression_to_c_expression(left)?),
            Box::new(spec_expression_to_c_expression(right)?),
        )),
        SpecExpression::BitwiseXor(left, right) => Some(CExpression::BitwiseXor(
            Box::new(spec_expression_to_c_expression(left)?),
            Box::new(spec_expression_to_c_expression(right)?),
        )),
        SpecExpression::BitwiseNot(value) => Some(CExpression::BitwiseNot(Box::new(
            spec_expression_to_c_expression(value)?,
        ))),
        _ => None,
    }
}

fn spec_proposition_to_c_expression(proposition: &SpecProposition) -> Option<CExpression> {
    match proposition {
        SpecProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let left = Box::new(spec_expression_to_c_expression(left)?);
            let right = Box::new(spec_expression_to_c_expression(right)?);
            Some(match operator {
                CComparisonOperator::Equal => CExpression::Equal(left, right),
                CComparisonOperator::NotEqual => CExpression::NotEqual(left, right),
                CComparisonOperator::LessThan => CExpression::LessThan(left, right),
                CComparisonOperator::LessEqual => CExpression::LessEqual(left, right),
                CComparisonOperator::GreaterThan => CExpression::GreaterThan(left, right),
                CComparisonOperator::GreaterEqual => CExpression::GreaterEqual(left, right),
            })
        }
        SpecProposition::And(left, right) => Some(CExpression::And(
            Box::new(spec_proposition_to_c_expression(left)?),
            Box::new(spec_proposition_to_c_expression(right)?),
        )),
        SpecProposition::Or(left, right) => Some(CExpression::Or(
            Box::new(spec_proposition_to_c_expression(left)?),
            Box::new(spec_proposition_to_c_expression(right)?),
        )),
        SpecProposition::Not(body) => Some(CExpression::Not(Box::new(
            spec_proposition_to_c_expression(body)?,
        ))),
        _ => None,
    }
}

fn collect_loop_invariants(
    statement: &CStatement,
    next_index: &mut usize,
    invariants: &mut BTreeMap<usize, Vec<CExpression>>,
) {
    match statement {
        CStatement::While {
            invariant_checks,
            body,
            ..
        } => {
            let index = *next_index;
            *next_index += 1;
            let conditions = invariant_checks
                .iter()
                .filter_map(|check| spec_proposition_to_c_expression(check.proposition()))
                .collect::<Vec<_>>();
            if !conditions.is_empty() {
                invariants.insert(index, conditions);
            }
            collect_loop_invariants(body, next_index, invariants);
        }
        CStatement::Seq(first, second) => {
            collect_loop_invariants(first, next_index, invariants);
            collect_loop_invariants(second, next_index, invariants);
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_loop_invariants(then_branch, next_index, invariants);
            collect_loop_invariants(else_branch, next_index, invariants);
        }
        CStatement::Switch { cases, .. } => {
            for case in cases {
                collect_loop_invariants(&case.body, next_index, invariants);
            }
        }
        CStatement::ContinueWithStep { step } => {
            collect_loop_invariants(step, next_index, invariants)
        }
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assign { .. }
        | CStatement::CallAssign { .. }
        | CStatement::Call { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::Update { .. } => {}
    }
}

fn loop_at_index<'a>(
    statement: &'a CStatement,
    target: usize,
    next_index: &mut usize,
) -> Option<&'a CStatement> {
    match statement {
        CStatement::While { body, .. } => {
            let index = *next_index;
            *next_index += 1;
            if index == target {
                Some(statement)
            } else {
                loop_at_index(body, target, next_index)
            }
        }
        CStatement::Seq(first, second) => loop_at_index(first, target, next_index)
            .or_else(|| loop_at_index(second, target, next_index)),
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => loop_at_index(then_branch, target, next_index)
            .or_else(|| loop_at_index(else_branch, target, next_index)),
        CStatement::Switch { cases, .. } => cases
            .iter()
            .find_map(|case| loop_at_index(&case.body, target, next_index)),
        CStatement::ContinueWithStep { step } => loop_at_index(step, target, next_index),
        _ => None,
    }
}

/// Compares two C statements while ignoring proof annotations. A verified
/// frontier rule may carry nested invariant checks that the partial function
/// used for contract certification intentionally omits; its executable shape
/// must still be the exact loop shape from the source body.
fn same_statement_shape(left: &CStatement, right: &CStatement) -> bool {
    match (left, right) {
        (CStatement::Seq(left_first, left_second), CStatement::Seq(right_first, right_second)) => {
            same_statement_shape(left_first, right_first)
                && same_statement_shape(left_second, right_second)
        }
        (
            CStatement::If {
                condition: left_condition,
                then_branch: left_then,
                else_branch: left_else,
            },
            CStatement::If {
                condition: right_condition,
                then_branch: right_then,
                else_branch: right_else,
            },
        ) => {
            left_condition == right_condition
                && same_statement_shape(left_then, right_then)
                && same_statement_shape(left_else, right_else)
        }
        (
            CStatement::While {
                condition: left_condition,
                do_while: left_do_while,
                body: left_body,
                ..
            },
            CStatement::While {
                condition: right_condition,
                do_while: right_do_while,
                body: right_body,
                ..
            },
        ) => {
            left_condition == right_condition
                && left_do_while == right_do_while
                && same_statement_shape(left_body, right_body)
        }
        (
            CStatement::Switch {
                expression: left_expression,
                cases: left_cases,
            },
            CStatement::Switch {
                expression: right_expression,
                cases: right_cases,
            },
        ) => {
            left_expression == right_expression
                && left_cases.len() == right_cases.len()
                && left_cases.iter().zip(right_cases).all(|(left, right)| {
                    left.value == right.value && same_statement_shape(&left.body, &right.body)
                })
        }
        (
            CStatement::ContinueWithStep { step: left_step },
            CStatement::ContinueWithStep { step: right_step },
        ) => same_statement_shape(left_step, right_step),
        _ => left == right,
    }
}

fn merge_verified_loop_invariants(
    function_name: &str,
    source_body: &CStatement,
    rules: &[CVerifiedLoopRule],
    invariants: &mut BTreeMap<usize, Vec<CExpression>>,
) -> Result<(), CTerminationError> {
    for rule in rules {
        let Some(index) = rule.loop_index else {
            continue;
        };
        let mut next_index = 0;
        let Some(source_loop) = loop_at_index(source_body, index, &mut next_index) else {
            return Err(error(format!(
                "verified loop rule for `{function_name}` refers to nonexistent loop {index}"
            )));
        };
        if !same_statement_shape(source_loop, &rule.loop_statement) {
            return Err(error(format!(
                "verified loop rule for `{function_name}` does not match loop {index}'s source shape"
            )));
        }
        let CStatement::While {
            invariant_checks, ..
        } = &rule.loop_statement
        else {
            return Err(error(format!(
                "verified loop rule for `{function_name}` is not a while loop"
            )));
        };
        let conditions = invariant_checks
            .iter()
            .filter_map(|check| spec_proposition_to_c_expression(check.proposition()))
            .collect::<Vec<_>>();
        if conditions.is_empty() {
            continue;
        }
        if let Some(existing) = invariants.get(&index) {
            if existing != &conditions {
                return Err(error(format!(
                    "verified loop rules for `{function_name}` disagree on loop {index} invariants"
                )));
            }
        } else {
            invariants.insert(index, conditions);
        }
    }
    Ok(())
}

fn ranking_proves(context: &PureFactContext, proposition: &Proposition) -> bool {
    if context.proves(proposition) {
        return true;
    }
    let premises = context
        .condition_facts
        .iter()
        .map(|(condition, value)| Proposition::ConditionIs(condition.clone(), *value))
        .collect::<Vec<_>>();
    crate::kernel::proof::fact_reasoning::check_signed_affine_arithmetic(proposition, &premises)
        .is_ok()
}

fn ranking_proves_lexicographic_decrease(
    context: &PureFactContext,
    pre_terms: &[Bitvector32Term],
    post_terms: &[Bitvector32Term],
) -> bool {
    if pre_terms.is_empty() || pre_terms.len() != post_terms.len() {
        return false;
    }
    (0..pre_terms.len()).any(|pivot| {
        let mut pivot_context = context.clone();
        for index in 0..pivot {
            pivot_context = pivot_context.assume_condition(
                ConditionTerm::equal(post_terms[index].clone(), pre_terms[index].clone()),
                true,
            );
        }
        ranking_proves(
            &pivot_context,
            &Proposition::ConditionIs(
                ConditionTerm::signed_less_than(
                    post_terms[pivot].clone(),
                    pre_terms[pivot].clone(),
                ),
                true,
            ),
        )
    })
}

fn ranking_affine_form(term: &Bitvector32Term) -> (BTreeMap<Bitvector32Term, i64>, i64) {
    match term {
        Bitvector32Term::Constant(value) => (BTreeMap::new(), i64::from(*value as i32)),
        Bitvector32Term::Add(left, right) => {
            let (mut terms, constant) = ranking_affine_form(left);
            let (right_terms, right_constant) = ranking_affine_form(right);
            let constant = constant.saturating_add(right_constant);
            for (term, coefficient) in right_terms {
                let updated = terms
                    .get(&term)
                    .copied()
                    .unwrap_or_default()
                    .saturating_add(coefficient);
                if updated == 0 {
                    terms.remove(&term);
                } else {
                    terms.insert(term, updated);
                }
            }
            (terms, constant)
        }
        Bitvector32Term::Subtract(left, right) => {
            let (mut terms, constant) = ranking_affine_form(left);
            let (right_terms, right_constant) = ranking_affine_form(right);
            let constant = constant.saturating_sub(right_constant);
            for (term, coefficient) in right_terms {
                let updated = terms
                    .get(&term)
                    .copied()
                    .unwrap_or_default()
                    .saturating_sub(coefficient);
                if updated == 0 {
                    terms.remove(&term);
                } else {
                    terms.insert(term, updated);
                }
            }
            (terms, constant)
        }
        Bitvector32Term::Multiply(left, right) => {
            let left_constant = left.as_const().map(|value| i64::from(value as i32));
            let right_constant = right.as_const().map(|value| i64::from(value as i32));
            if let Some(constant) = left_constant {
                let (terms, right_constant) = ranking_affine_form(right);
                (
                    terms
                        .into_iter()
                        .map(|(term, coefficient)| (term, coefficient.saturating_mul(constant)))
                        .filter(|(_, coefficient)| *coefficient != 0)
                        .collect(),
                    right_constant.saturating_mul(constant),
                )
            } else if let Some(constant) = right_constant {
                let (terms, left_constant) = ranking_affine_form(left);
                (
                    terms
                        .into_iter()
                        .map(|(term, coefficient)| (term, coefficient.saturating_mul(constant)))
                        .filter(|(_, coefficient)| *coefficient != 0)
                        .collect(),
                    left_constant.saturating_mul(constant),
                )
            } else {
                let mut atom = BTreeMap::new();
                atom.insert(term.clone(), 1);
                (atom, 0)
            }
        }
        _ => {
            let mut atom = BTreeMap::new();
            atom.insert(term.clone(), 1);
            (atom, 0)
        }
    }
}

fn canonical_ranking_term(term: &Bitvector32Term) -> Bitvector32Term {
    let (terms, constant) = ranking_affine_form(term);
    let mut result = Bitvector32Term::Constant(0);
    for (term, coefficient) in terms {
        let magnitude = coefficient.unsigned_abs();
        let factor = if magnitude == 1 {
            term
        } else {
            Bitvector32Term::multiply(Bitvector32Term::Constant(magnitude as u32), term)
        };
        result = if coefficient < 0 {
            Bitvector32Term::subtract(result, factor)
        } else {
            Bitvector32Term::add(result, factor)
        };
    }
    if constant < 0 {
        Bitvector32Term::subtract(
            result,
            Bitvector32Term::Constant(constant.unsigned_abs() as u32),
        )
    } else {
        Bitvector32Term::add(result, Bitvector32Term::Constant(constant as u32))
    }
}

fn check_loops(
    statement: &CStatement,
    supplied: &BTreeMap<usize, Vec<CExpression>>,
    entry_conditions: &[CExpression],
    invariants: &BTreeMap<usize, Vec<CExpression>>,
    next_index: &mut usize,
) -> Result<bool, CTerminationError> {
    match statement {
        CStatement::Seq(first, second) => {
            Ok(
                check_loops(first, supplied, entry_conditions, invariants, next_index)?
                    && check_loops(second, supplied, entry_conditions, invariants, next_index)?,
            )
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => Ok(check_loops(
            then_branch,
            supplied,
            entry_conditions,
            invariants,
            next_index,
        )? && check_loops(
            else_branch,
            supplied,
            entry_conditions,
            invariants,
            next_index,
        )?),
        CStatement::While {
            condition, body, ..
        } => {
            let index = *next_index;
            *next_index += 1;
            let nested_terminate =
                check_loops(body, supplied, entry_conditions, invariants, next_index)?;
            let Some(measures) = supplied.get(&index) else {
                return Ok(false);
            };
            if measures.is_empty() {
                return Err(error(format!(
                    "loop {index} has an empty termination measure"
                )));
            }
            let mut measure_variables = BTreeSet::new();
            for measure in measures {
                collect_c_expression_variables(measure, &mut measure_variables);
            }
            let paths = loop_paths(
                body,
                &measure_variables,
                vec![LoopRankingPath {
                    aliases: BTreeMap::new(),
                    conditions: Vec::new(),
                }],
            )?;
            if paths.is_empty() {
                return Ok(nested_terminate);
            }
            for path in paths {
                let post_measures = measures
                    .iter()
                    .map(|measure| resolve_loop_c_expression_aliases(measure, &path.aliases))
                    .collect::<Vec<_>>();
                let mut names = measure_variables.clone();
                for entry_condition in entry_conditions {
                    collect_c_expression_variables(entry_condition, &mut names);
                }
                if let Some(loop_invariants) = invariants.get(&index) {
                    for invariant in loop_invariants {
                        collect_c_expression_variables(invariant, &mut names);
                    }
                }
                collect_c_expression_variables(condition, &mut names);
                for post_measure in &post_measures {
                    collect_c_expression_variables(post_measure, &mut names);
                }
                for (path_condition, _) in &path.conditions {
                    collect_c_expression_variables(path_condition, &mut names);
                }
                let variables = ranking_variable_map(&names);
                let pre_terms = measures
                    .iter()
                    .map(|measure| {
                        ranking_term(measure, &variables).map(|term| canonical_ranking_term(&term))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let post_terms = post_measures
                    .iter()
                    .map(|measure| {
                        ranking_term(measure, &variables).map(|term| canonical_ranking_term(&term))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let mut context = PureFactContext::new();
                for entry_condition in entry_conditions {
                    context = assume_ranking_condition(context, entry_condition, true, &variables)?;
                }
                if let Some(loop_invariants) = invariants.get(&index) {
                    for invariant in loop_invariants {
                        context = assume_ranking_condition(context, invariant, true, &variables)?;
                    }
                }
                context = assume_ranking_condition(context, condition, true, &variables)?;
                for (path_condition, value) in &path.conditions {
                    context =
                        assume_ranking_condition(context, path_condition, *value, &variables)?;
                }
                for pre_term in &pre_terms {
                    let pre_positive = Proposition::ConditionIs(
                        ConditionTerm::signed_less_than(
                            Bitvector32Term::Constant(0),
                            pre_term.clone(),
                        ),
                        true,
                    );
                    if ranking_proves(&context, &pre_positive) {
                        context = context.assume_condition(
                            ConditionTerm::signed_less_than(
                                Bitvector32Term::Constant(0),
                                pre_term.clone(),
                            ),
                            true,
                        );
                    }
                }
                let pre_proved = pre_terms.iter().all(|pre_term| {
                    ranking_proves(
                        &context,
                        &Proposition::ConditionIs(
                            ConditionTerm::signed_less_equal(
                                Bitvector32Term::Constant(0),
                                pre_term.clone(),
                            ),
                            true,
                        ),
                    )
                });
                let post_proved = post_terms.iter().all(|post_term| {
                    ranking_proves(
                        &context,
                        &Proposition::ConditionIs(
                            ConditionTerm::signed_less_equal(
                                Bitvector32Term::Constant(0),
                                post_term.clone(),
                            ),
                            true,
                        ),
                    )
                });
                let decreases_proved =
                    ranking_proves_lexicographic_decrease(&context, &pre_terms, &post_terms);
                if !pre_proved || !post_proved || !decreases_proved {
                    let display = termination_measures_display(measures);
                    return Err(error(format!(
                        "loop {index} does not decrease `{display}` to a nonnegative value on every back edge"
                    )));
                }
            }
            Ok(nested_terminate)
        }
        CStatement::Switch { cases, .. } => {
            let mut nested_terminate = true;
            for case in cases {
                nested_terminate &= check_loops(
                    &case.body,
                    supplied,
                    entry_conditions,
                    invariants,
                    next_index,
                )?;
            }
            Ok(nested_terminate)
        }
        CStatement::ContinueWithStep { step } => {
            check_loops(step, supplied, entry_conditions, invariants, next_index)
        }
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assign { .. }
        | CStatement::CallAssign { .. }
        | CStatement::Call { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::Update { .. } => Ok(true),
    }
}

fn reachable(start: &str, target: &str, calls: &BTreeMap<String, BTreeSet<String>>) -> bool {
    let mut pending = vec![start];
    let mut visited = BTreeSet::new();
    while let Some(name) = pending.pop() {
        if !visited.insert(name) {
            continue;
        }
        if name == target {
            return true;
        }
        if let Some(next) = calls.get(name) {
            pending.extend(next.iter().map(String::as_str));
        }
    }
    false
}

/// Checks untrusted ranking plans against exact partially-correct function
/// rules and returns the independently usable subset proved to terminate.
pub fn c_verified_function_termination_rules(
    partial_rules: &[CVerifiedFunctionRule],
    plan_entries: &[CFunctionTerminationPlan],
    verified_loop_rules: &BTreeMap<String, Vec<CVerifiedLoopRule>>,
) -> Result<Vec<CVerifiedFunctionTerminationRule>, CTerminationError> {
    let functions = partial_rules
        .iter()
        .map(|rule| (rule.function.name.clone(), &rule.function))
        .collect::<BTreeMap<_, _>>();
    let plans = plan_entries
        .iter()
        .map(|plan| (plan.function_name.clone(), plan))
        .collect::<BTreeMap<_, _>>();
    if plans.len() != plan_entries.len() {
        return Err(error("termination plans contain a duplicate function"));
    }

    let calls = functions
        .iter()
        .map(|(name, function)| {
            let mut found = BTreeSet::new();
            statement_calls(&function.source_body, &mut found);
            (name.clone(), found)
        })
        .collect::<BTreeMap<_, _>>();

    let mut components = Vec::<BTreeSet<String>>::new();
    for name in functions.keys() {
        let component = functions
            .keys()
            .filter(|other| reachable(name, other, &calls) && reachable(other, name, &calls))
            .cloned()
            .collect::<BTreeSet<_>>();
        if !components.contains(&component) {
            components.push(component);
        }
    }

    let mut structurally_terminating = BTreeMap::new();
    for component in &components {
        let recursive = component.len() > 1
            || component
                .iter()
                .any(|name| calls[name].contains(name.as_str()));
        let mut parameter_indices = BTreeMap::new();
        let mut structural_requirement = None;
        if recursive {
            if component.iter().any(|name| {
                plans
                    .get(name)
                    .and_then(|plan| plan.recursive_measure.as_ref())
                    .is_none()
            }) {
                for name in component {
                    structurally_terminating.insert(name.clone(), false);
                }
                continue;
            }
            let has_resource_measure = component.iter().any(|name| {
                matches!(
                    plans[name].recursive_measure,
                    Some(CFunctionTerminationMeasure::ResourceRequirement(_))
                )
            });
            if has_resource_measure {
                if component.len() != 1 {
                    return Err(error(
                        "structural resource termination currently supports direct recursion only",
                    ));
                }
                let name = component.first().expect("recursive component is nonempty");
                let Some(CFunctionTerminationMeasure::ResourceRequirement(index)) =
                    plans[name].recursive_measure
                else {
                    return Err(error(
                        "a recursive component cannot mix numeric and structural measures",
                    ));
                };
                structural_requirement = Some(index);
            } else {
                for name in component {
                    let function = functions[name];
                    let Some(CFunctionTerminationMeasure::NumericParameter(index)) =
                        plans[name].recursive_measure
                    else {
                        return Err(error(
                            "a recursive component cannot mix numeric and structural measures",
                        ));
                    };
                    let parameter = function.parameters.get(index).ok_or_else(|| {
                        error(format!(
                            "termination parameter index is invalid for `{name}`"
                        ))
                    })?;
                    if parameter.c_type != CType::Int32 {
                        return Err(error(format!(
                            "termination parameter `{}` in `{name}` must have type int32",
                            parameter.name
                        )));
                    }
                    parameter_indices.insert(name.clone(), index);
                }
            }
        } else if let Some(name) = component.first()
            && plans
                .get(name)
                .is_some_and(|plan| plan.recursive_measure.is_some())
        {
            return Err(error(format!(
                "function-level `decreases` on nonrecursive function `{name}` has no recursive edge to rank"
            )));
        }

        let mut component_ok = true;
        for name in component {
            let function = functions[name];
            let empty = BTreeMap::new();
            let loop_measures = plans.get(name).map_or(&empty, |plan| &plan.loop_measures);
            for measures in loop_measures.values() {
                for measure in measures {
                    reject_address_escaped_expression_measure(
                        name,
                        measure,
                        &function.source_body,
                    )?;
                }
            }
            let entry_conditions = function
                .contract_requires()
                .iter()
                .filter_map(spec_proposition_to_c_expression)
                .collect::<Vec<_>>();
            let mut invariant_index = 0;
            let mut invariants = BTreeMap::new();
            collect_loop_invariants(&function.body, &mut invariant_index, &mut invariants);
            if let Some(rules) = verified_loop_rules.get(name) {
                merge_verified_loop_invariants(
                    name,
                    &function.source_body,
                    rules,
                    &mut invariants,
                )?;
            }
            let mut next_loop = 0;
            component_ok &= check_loops(
                &function.source_body,
                loop_measures,
                &entry_conditions,
                &invariants,
                &mut next_loop,
            )?;
            if loop_measures.keys().any(|index| *index >= next_loop) {
                return Err(error(format!(
                    "termination plan for `{name}` refers to a nonexistent loop"
                )));
            }
            if recursive {
                if let Some(requirement_index) = structural_requirement {
                    let measure = structural_resource_children(function, requirement_index)?;
                    let conditions = if measure.guard_is_precondition {
                        vec![(measure.guard.clone(), true)]
                    } else {
                        Vec::new()
                    };
                    structural_recursion_paths(
                        &function.source_body,
                        function,
                        &measure.arguments,
                        &measure.children,
                        &measure.guard,
                        vec![StructuralRecursionPath {
                            aliases: BTreeMap::new(),
                            conditions,
                        }],
                    )?;
                } else {
                    let index = parameter_indices[name];
                    let measure = &function.parameters[index].name;
                    reject_address_escaped_measure(name, measure, &function.source_body)?;
                    recursion_paths(
                        &function.source_body,
                        measure,
                        component,
                        &parameter_indices,
                        vec![i64::MIN / 2],
                    )?;
                }
            }
        }
        for name in component {
            structurally_terminating.insert(name.clone(), component_ok);
        }
    }

    let mut terminating = BTreeSet::new();
    loop {
        let before = terminating.len();
        for component in &components {
            if component.iter().all(|name| structurally_terminating[name])
                && component.iter().all(|name| {
                    calls[name]
                        .iter()
                        .all(|callee| component.contains(callee) || terminating.contains(callee))
                })
            {
                terminating.extend(component.iter().cloned());
            }
        }
        if terminating.len() == before {
            break;
        }
    }

    Ok(partial_rules
        .iter()
        .filter(|rule| terminating.contains(rule.function.name()))
        .map(|rule| CVerifiedFunctionTerminationRule {
            function: rule.function.clone(),
        })
        .collect())
}

#[cfg(test)]
mod address_escape_tests {
    use super::*;
    use std::sync::Arc;

    fn variable(name: &str) -> CExpression {
        CExpression::Variable(name.to_string())
    }

    fn address_of(name: &str) -> CExpression {
        CExpression::AddressOf(Box::new(variable(name)))
    }

    #[test]
    fn store_through_escaped_address_is_detected() {
        // p = &i; *p = q;
        let escape = CStatement::Assign {
            name: "p".to_string(),
            expression: address_of("i"),
        };
        let store = CStatement::Store {
            pointer: variable("p"),
            value: variable("q"),
        };
        let body = CStatement::Seq(Arc::new(escape), Arc::new(store));
        assert!(statement_takes_address_of(&body, "i"));
        assert!(!statement_takes_address_of(&body, "q"));
        assert!(reject_address_escaped_measure("spin", "i", &body).is_err());
        assert!(reject_address_escaped_measure("spin", "q", &body).is_ok());
    }

    #[test]
    fn helper_call_receiving_the_address_is_detected() {
        let call = CStatement::Call {
            function_name: "reset".to_string(),
            arguments: vec![address_of("n")],
        };
        assert!(statement_takes_address_of(&call, "n"));
        assert!(reject_address_escaped_measure("f", "n", &call).is_err());
    }

    #[test]
    fn escape_inside_a_loop_or_branch_body_is_detected() {
        let escape = CStatement::Assign {
            name: "p".to_string(),
            expression: CExpression::Add(Box::new(address_of("n")), Box::new(variable("k"))),
        };
        let branch = CStatement::If {
            condition: variable("c"),
            then_branch: Box::new(CStatement::Skip),
            else_branch: Box::new(escape),
        };
        let body = CStatement::While {
            condition: variable("c"),
            invariant: Vec::new(),
            invariant_checks: Vec::new(),
            effect_checks: Vec::new(),
            do_while: false,
            body: Box::new(branch),
        };
        assert!(statement_takes_address_of(&body, "n"));
        assert!(!statement_takes_address_of(&body, "c"));
    }
}
