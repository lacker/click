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

fn statement_calls(statement: &CStatement, calls: &mut BTreeSet<String>) {
    match statement {
        CStatement::CallAssign { function_name, .. } => {
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
        CStatement::Skip
        | CStatement::Declare { .. }
        | CStatement::Assign { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. } => {}
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
        | CStatement::Declare { .. }
        | CStatement::Assert { .. }
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. } => Ok(lower_bounds),
        CStatement::Return(_) => Ok(Vec::new()),
        CStatement::Assign { name, .. } if name == measure => Err(error(format!(
            "termination measure `{measure}` is reassigned; this first implementation requires an unchanged function parameter"
        ))),
        CStatement::Assign { .. } => Ok(lower_bounds),
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
    }
}

fn loop_paths(
    statement: &CStatement,
    measure: &str,
    offsets: Vec<i64>,
) -> Result<Vec<i64>, CTerminationError> {
    match statement {
        CStatement::Skip
        | CStatement::Declare { .. }
        | CStatement::Assert { .. }
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. } => Ok(offsets),
        CStatement::Return(_) => Ok(Vec::new()),
        CStatement::Assign { name, expression } if name == measure => {
            let step = variable_minus_positive(expression, measure).ok_or_else(|| {
                error(format!(
                    "loop measure `{measure}` must be updated as `{measure} = {measure} - K` for a positive constant K"
                ))
            })?;
            Ok(offsets.into_iter().map(|offset| offset - step).collect())
        }
        CStatement::Assign { .. } => Ok(offsets),
        CStatement::CallAssign { target, .. } if target == measure => Err(error(format!(
            "loop measure `{measure}` is overwritten by a call result"
        ))),
        CStatement::CallAssign { .. } => Ok(offsets),
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
        CStatement::Skip
        | CStatement::Declare { .. }
        | CStatement::Assign { .. }
        | CStatement::CallAssign { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. } => Ok(true),
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
        if recursive {
            if component.iter().any(|name| {
                plans
                    .get(name)
                    .and_then(|plan| plan.recursive_parameter)
                    .is_none()
            }) {
                for name in component {
                    structurally_terminating.insert(name.clone(), false);
                }
                continue;
            }
            for name in component {
                let function = functions[name];
                let index = plans[name].recursive_parameter.unwrap();
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
        } else if let Some(name) = component.first()
            && plans
                .get(name)
                .is_some_and(|plan| plan.recursive_parameter.is_some())
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
            let mut next_loop = 0;
            component_ok &= check_loops(&function.source_body, loop_measures, &mut next_loop)?;
            if loop_measures.keys().any(|index| *index >= next_loop) {
                return Err(error(format!(
                    "termination plan for `{name}` refers to a nonexistent loop"
                )));
            }
            if recursive {
                let index = parameter_indices[name];
                let measure = &function.parameters[index].name;
                recursion_paths(
                    &function.source_body,
                    measure,
                    component,
                    &parameter_indices,
                    vec![i64::MIN / 2],
                )?;
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
