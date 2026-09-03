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
        CStatement::Return(_) => Ok(Vec::new()),
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
        | CStatement::Declare { .. } => false,
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
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Declare { .. }
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
        | CStatement::Assert { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::Update { .. } => Ok(lower_bounds),
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

fn loop_paths(
    statement: &CStatement,
    measure: &str,
    offsets: Vec<i64>,
) -> Result<Vec<i64>, CTerminationError> {
    match statement {
        CStatement::Skip
        | CStatement::Continue
        | CStatement::Declare { .. }
        | CStatement::Assert { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::Update { .. } => Ok(offsets),
        CStatement::Return(_) | CStatement::Break => Ok(Vec::new()),
        CStatement::Assign { name, expression } if name == measure => {
            let step = variable_minus_positive(expression, measure).ok_or_else(|| {
                error(format!(
                    "loop measure `{measure}` must be updated as `{measure} = {measure} - K` for a positive constant K"
                ))
            })?;
            Ok(offsets.into_iter().map(|offset| offset - step).collect())
        }
        CStatement::Assign { .. } => Ok(offsets),
        CStatement::HeapAllocate { target, .. } if target == measure => Err(error(format!(
            "loop measure `{measure}` is overwritten by an allocation result"
        ))),
        CStatement::HeapAllocate { .. } => Ok(offsets),
        CStatement::CallAssign { target, .. } if target == measure => Err(error(format!(
            "loop measure `{measure}` is overwritten by a call result"
        ))),
        CStatement::CallAssign { .. } => Ok(offsets),
        CStatement::Call { .. } => Ok(offsets),
        CStatement::Seq(first, second) => {
            loop_paths(second, measure, loop_paths(first, measure, offsets)?)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            let mut paths = loop_paths(then_branch, measure, offsets.clone())?;
            paths.extend(loop_paths(else_branch, measure, offsets)?);
            Ok(paths)
        }
        CStatement::While { .. } => Err(error(
            "nested loops in one ranking proof are not yet supported",
        )),
        CStatement::Switch { cases, .. } => {
            let mut paths = Vec::new();
            for case in cases {
                paths.extend(loop_paths(&case.body, measure, offsets.clone())?);
            }
            Ok(paths)
        }
    }
}

fn check_loops(
    statement: &CStatement,
    supplied: &BTreeMap<usize, String>,
    next_index: &mut usize,
) -> Result<bool, CTerminationError> {
    match statement {
        CStatement::Seq(first, second) => {
            Ok(check_loops(first, supplied, next_index)?
                && check_loops(second, supplied, next_index)?)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => Ok(check_loops(then_branch, supplied, next_index)?
            && check_loops(else_branch, supplied, next_index)?),
        CStatement::While {
            condition, body, ..
        } => {
            let index = *next_index;
            *next_index += 1;
            let nested_terminate = check_loops(body, supplied, next_index)?;
            let Some(measure) = supplied.get(&index) else {
                return Ok(false);
            };
            let lower_bound = refined_lower_bound(condition, measure, true, i64::MIN / 2);
            let offsets = loop_paths(body, measure, vec![0])?;
            if offsets.is_empty() {
                return Ok(nested_terminate);
            }
            if offsets
                .iter()
                .any(|offset| *offset >= 0 || lower_bound.saturating_add(*offset) < 0)
            {
                return Err(error(format!(
                    "loop {index} does not decrease `{measure}` to a nonnegative value on every back edge"
                )));
            }
            Ok(nested_terminate)
        }
        CStatement::Switch { cases, .. } => {
            let mut nested_terminate = true;
            for case in cases {
                nested_terminate &= check_loops(&case.body, supplied, next_index)?;
            }
            Ok(nested_terminate)
        }
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Declare { .. }
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
            for measure in loop_measures.values() {
                reject_address_escaped_measure(name, measure, &function.source_body)?;
            }
            let mut next_loop = 0;
            component_ok &= check_loops(&function.source_body, loop_measures, &mut next_loop)?;
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
