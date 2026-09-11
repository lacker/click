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
            pointee_volatile,
            pointee_constant,
        } => Cast {
            expression: unary(body),
            target_type: *target_type,
            pointee_volatile: *pointee_volatile,
            pointee_constant: *pointee_constant,
        },
        FloatClassification {
            expression: body,
            classification,
        } => FloatClassification {
            expression: unary(body),
            classification: *classification,
        },
        FloatNegate(body) => FloatNegate(unary(body)),
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
            volatile,
        } => TypedLoad {
            pointer: unary(pointer),
            value_type: *value_type,
            volatile: *volatile,
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
    /// Direct recursive children named through a `let` witness of the
    /// definition rather than a C expression of its parameters.
    witness_children: Vec<WitnessChildMeasure>,
    guard: CExpression,
    guard_is_precondition: bool,
}

struct WitnessChildMeasure {
    definition: CCompositeResourceDefinition,
    /// Each child argument: a witness of `definition`, or a body expression.
    arguments: Vec<CExpression>,
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
    measure: &StructuralResourceMeasure,
    path: &StructuralRecursionPath,
) -> Result<(), CTerminationError> {
    if function_name != function.name() {
        return Ok(());
    }
    if !path.conditions.iter().any(|(condition, value)| {
        branch_establishes_structural_guard(condition, *value, &measure.guard)
    }) {
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
    let call_measure_arguments = measure
        .arguments
        .iter()
        .map(|argument| substitute_c_expression_variables(argument, &parameter_substitutions))
        .collect::<Vec<_>>();
    if !measure.children.contains(&call_measure_arguments)
        && !call_passes_witness_child(function, measure, &call_measure_arguments)
    {
        return Err(error(format!(
            "recursive call to `{function_name}` does not pass a direct contained child of its structural resource measure"
        )));
    }
    Ok(())
}

fn structural_recursion_paths(
    statement: &CStatement,
    function: &CFunction,
    measure: &StructuralResourceMeasure,
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
        | CStatement::CopyAggregate { .. }
        | CStatement::Update { .. } => Ok(paths),
        CStatement::ContinueWithStep { step } => {
            structural_recursion_paths(step, function, measure, paths)
        }
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
                    measure,
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
                check_structural_recursive_call(function_name, arguments, function, measure, path)?;
            }
            Ok(paths)
        }
        CStatement::Seq(first, second) => structural_recursion_paths(
            second,
            function,
            measure,
            structural_recursion_paths(first, function, measure, paths)?,
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
            let mut paths = structural_recursion_paths(then_branch, function, measure, then_paths)?;
            paths.extend(structural_recursion_paths(
                else_branch,
                function,
                measure,
                else_paths,
            )?);
            Ok(paths)
        }
        CStatement::While {
            condition, body, ..
        } => {
            let mut body_paths = Vec::new();
            for path in &paths {
                let condition = resolve_c_expression_aliases(condition, &path.aliases);
                let mut body_path = path.clone();
                body_path.conditions.push((condition, true));
                body_paths.push(body_path);
            }
            structural_recursion_paths(body, function, measure, body_paths)?;
            Ok(paths)
        }
        CStatement::Switch { cases, .. } => {
            let incoming_paths = paths;
            let mut paths = Vec::new();
            for case in cases {
                paths.extend(structural_recursion_paths(
                    &case.body,
                    function,
                    measure,
                    incoming_paths.clone(),
                )?);
            }
            Ok(paths)
        }
    }
}

fn c_expression_mentions_variable(expression: &CExpression, variable: &str) -> bool {
    let mut substitutions = BTreeMap::new();
    substitutions.insert(
        variable.to_string(),
        CExpression::Value(CValue::Int32(Bitvector32Term::Constant(0))),
    );
    substitute_c_expression_variables(expression, &substitutions) != *expression
}

/// Assumes one evaluation path's facts. Loadability obligations are the
/// uninterpreted reads the structural comparison already relies on; every
/// other obligation must already be decided.
///
/// "Decided" is an exact route only: the frozen condition checker for a bare
/// condition, and exact fact lookup for anything else. This helper has no
/// proof site to emit an undischarged obligation to, so an obligation the
/// exact routes do not settle refuses the witness match rather than being
/// discharged by a general proof search.
fn assume_structural_path(
    assumptions: &mut PureFactContext,
    facts: &[ExecutionPureFact],
    obligations: &[ProofObligation],
) -> Option<()> {
    for obligation in obligations {
        let proposition = obligation.proposition();
        let decided = match proposition {
            Proposition::CMemoryLoadable { .. } => true,
            Proposition::ConditionIs(condition, value) => {
                assumptions.decide(condition) == Some(*value)
            }
            proposition => assumptions.proves_exact(proposition),
        };
        if !decided {
            return None;
        }
        *assumptions = assumptions.clone().assume_proposition(proposition.clone());
    }
    for fact in facts {
        *assumptions = assumptions
            .clone()
            .assume_proposition(fact.proposition().clone());
    }
    Some(())
}

fn evaluate_structural_c_expression(
    state: &CState,
    expression: &CExpression,
    assumptions: &mut PureFactContext,
    budget: &mut ExecutionBudget,
) -> Option<CValue> {
    let paths = evaluate_c_expression_paths(state, expression, assumptions, budget).ok()?;
    let [path] = paths.as_slice() else {
        return None;
    };
    let CExpressionOutcome::Value(value) = &path.outcome else {
        return None;
    };
    assume_structural_path(assumptions, &path.facts, &path.obligations)?;
    Some(value.clone())
}

/// Whether a recursive call's measure arguments name a witness child of the
/// entry measure. A `let` witness has no C spelling, so the exact definition
/// is instantiated over a symbolic entry state with no memory: its guard and
/// `where` facts are assumed, the call's arguments are evaluated there, and
/// the pure kernel decides the argument is the witness pointer. Loads are
/// the same uninterpreted reads the syntactic child comparison relies on.
fn call_passes_witness_child(
    function: &CFunction,
    measure: &StructuralResourceMeasure,
    call_measure_arguments: &[CExpression],
) -> bool {
    const PARAMETER_VARIABLE_BASE: u64 = 4_200_000_000;
    const WITNESS_VARIABLE_BASE: u64 = 4_250_000_000;
    if measure.witness_children.is_empty() {
        return false;
    }
    let mut budget = ExecutionBudget::default();
    let entry_assumptions = PureFactContext::new()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    let mut parameter_state = CState::new();
    for (index, parameter) in function.parameters().iter().enumerate() {
        let variable = Variable(PARAMETER_VARIABLE_BASE + index as u64);
        let value = if parameter.c_type().is_pointer() {
            CValue::typed_pointer(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(variable), 1),
                },
                parameter.c_type(),
            )
        } else {
            symbolic_call_result(parameter.c_type(), variable)
        };
        parameter_state
            .locals
            .set_typed(parameter.name().to_string(), value, parameter.c_type());
    }
    'children: for child in &measure.witness_children {
        let definition = &child.definition;
        if child.arguments.len() != call_measure_arguments.len() {
            continue;
        }
        let mut assumptions = entry_assumptions.clone();
        let mut body_state = CState::new();
        for (parameter, argument) in definition.parameters().iter().zip(&measure.arguments) {
            let Some(value) = evaluate_structural_c_expression(
                &parameter_state,
                argument,
                &mut assumptions,
                &mut budget,
            ) else {
                continue 'children;
            };
            if value.c_type() != parameter.c_type() {
                continue 'children;
            }
            body_state
                .locals
                .set_typed(parameter.name().to_string(), value, parameter.c_type());
        }
        for (index, witness) in definition.witnesses().iter().enumerate() {
            let pointer = Pointer::symbolic(Variable(WITNESS_VARIABLE_BASE + index as u64));
            body_state.locals.set_typed(
                witness.name().to_string(),
                CValue::typed_pointer(pointer, witness.c_type()),
                witness.c_type(),
            );
        }
        for fact in definition.condition().into_iter().chain(definition.facts()) {
            let Ok(paths) = lower_spec_proposition_at_state_with_loop_entry(
                &body_state,
                fact,
                None,
                &assumptions,
                &mut budget,
            ) else {
                continue 'children;
            };
            let [path] = paths.as_slice() else {
                continue 'children;
            };
            if assume_structural_path(&mut assumptions, &path.facts, &path.obligations).is_none() {
                continue 'children;
            }
            assumptions = assumptions.assume_proposition(path.proposition.clone());
        }
        for (expected, actual) in child.arguments.iter().zip(call_measure_arguments) {
            let Some(expected) = evaluate_structural_c_expression(
                &body_state,
                expected,
                &mut assumptions,
                &mut budget,
            ) else {
                continue 'children;
            };
            let Some(actual) = evaluate_structural_c_expression(
                &parameter_state,
                actual,
                &mut assumptions,
                &mut budget,
            ) else {
                continue 'children;
            };
            let (CValue::Pointer(expected), CValue::Pointer(actual)) = (expected, actual) else {
                continue 'children;
            };
            let expected = expected.pointer();
            let actual = actual.pointer();
            if expected != actual
                && assumptions.decide(&ConditionTerm::pointer_equal(
                    actual.clone(),
                    expected.clone(),
                )) != Some(true)
            {
                continue 'children;
            }
        }
        return true;
    }
    false
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
    let mentions_witness = |expression: &CExpression| {
        definition
            .witnesses()
            .iter()
            .any(|witness| c_expression_mentions_variable(expression, witness.name()))
    };
    let mut children = Vec::new();
    let mut witness_children = Vec::new();
    for contained in definition.contains() {
        let CResourceSpec::Composite {
            name: child_name,
            arguments: child_arguments,
            ..
        } = contained
        else {
            continue;
        };
        if child_name != name {
            continue;
        }
        if child_arguments.iter().any(mentions_witness) {
            witness_children.push(WitnessChildMeasure {
                definition: definition.clone(),
                arguments: child_arguments.clone(),
            });
        } else {
            children.push(
                child_arguments
                    .iter()
                    .map(|argument| substitute_c_expression_variables(argument, &substitutions))
                    .collect::<Vec<_>>(),
            );
        }
    }
    if children.is_empty() && witness_children.is_empty() {
        return Err(error(format!(
            "resource measure `{name}` has no direct recursive child"
        )));
    }
    Ok(StructuralResourceMeasure {
        arguments: arguments.clone(),
        children,
        witness_children,
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
        FloatNegate(expression) | FloatClassification { expression, .. } => inner(expression),
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
        | FloatNegate(expression)
        | FloatClassification { expression, .. }
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
        CStatement::CopyAggregate { target, source, .. } => escapes(target) || escapes(source),
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

/// Rejects a loop `decreases` component naming a variable whose address
/// escapes, before the back-edge bundle is built. A store through that
/// pointer, here or inside a callee, could change the component without a
/// ranked update, so the declaration is refused rather than proved.
pub(super) fn c_reject_address_escaped_loop_measures(
    function_name: &str,
    measures: &[CExpression],
    body: &CStatement,
) -> Result<(), String> {
    for measure in measures {
        reject_address_escaped_expression_measure(function_name, measure, body)
            .map_err(|error| error.message)?;
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
        | CStatement::CopyAggregate { .. }
        | CStatement::Update { .. } => {}
    }
}

/// Collects the names this body declares, so a call through one of them is
/// not mistaken for a call to a like-named function.
fn statement_declared_variables(statement: &CStatement, names: &mut BTreeSet<String>) {
    match statement {
        CStatement::Declare { name, .. }
        | CStatement::DeclareAggregate { name, .. }
        | CStatement::CallAssign { target: name, .. }
        | CStatement::HeapAllocate { target: name, .. } => {
            names.insert(name.clone());
        }
        CStatement::Seq(first, second) => {
            statement_declared_variables(first, names);
            statement_declared_variables(second, names);
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            statement_declared_variables(then_branch, names);
            statement_declared_variables(else_branch, names);
        }
        CStatement::While { body, .. } => statement_declared_variables(body, names),
        CStatement::Switch { cases, .. } => {
            for case in cases {
                statement_declared_variables(&case.body, names);
            }
        }
        CStatement::ContinueWithStep { step } => statement_declared_variables(step, names),
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Assign { .. }
        | CStatement::Update { .. }
        | CStatement::Call { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::CopyAggregate { .. } => {}
    }
}

/// The names `function` binds as objects: its parameters and everything its
/// body declares.
fn function_object_names(function: &CFunction) -> BTreeSet<String> {
    let mut names = function
        .parameters()
        .iter()
        .map(|parameter| parameter.name().to_string())
        .collect::<BTreeSet<_>>();
    statement_declared_variables(&function.source_body, &mut names);
    names
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
        | CStatement::CopyAggregate { .. } => Ok(lower_bounds),
        CStatement::ContinueWithStep { step } => {
            recursion_paths(step, measure, component, parameter_indices, lower_bounds)
        }
        CStatement::Return(_) => Ok(Vec::new()),
        CStatement::Break => Ok(Vec::new()),
        CStatement::Assign { name, .. } if name == measure => Err(error(format!(
            "termination measure `{measure}` is reassigned; this first implementation requires an unchanged function parameter"
        ))),
        CStatement::Assign { .. } => Ok(lower_bounds),
        CStatement::Update {
            target: CExpression::Variable(name),
            ..
        } if name == measure => Err(error(format!(
            "termination measure `{measure}` is updated; this first implementation requires an unchanged function parameter"
        ))),
        CStatement::Update { .. } => Ok(lower_bounds),
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
        CStatement::While {
            condition, body, ..
        } => {
            for lower_bound in &lower_bounds {
                let body_lower_bound = refined_lower_bound(condition, measure, true, *lower_bound);
                recursion_paths(
                    body,
                    measure,
                    component,
                    parameter_indices,
                    vec![body_lower_bound],
                )?;
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

fn termination_measure_display(measure: &CExpression) -> String {
    use CExpression::*;
    let binary = |left: &CExpression, right: &CExpression, operator: &str| {
        format!(
            "{} {operator} {}",
            termination_measure_display(left),
            termination_measure_display(right)
        )
    };
    match measure {
        Variable(name) => name.clone(),
        Value(CValue::Int32(term)) | Value(CValue::UInt8(term)) => match term.as_const() {
            Some(value) => format!("{}", value as i32),
            None => format!("{measure:?}"),
        },
        Add(left, right) => binary(left, right, "+"),
        Subtract(left, right) => binary(left, right, "-"),
        Multiply(left, right) => binary(left, right, "*"),
        Divide(left, right) => binary(left, right, "/"),
        Remainder(left, right) => binary(left, right, "%"),
        _ => format!("{measure:?}"),
    }
}

/// The kernel term for one `decreases` component at one C state.
///
/// A ranking component is a scalar int32 expression over the loop's own
/// unaddressed variables, so its value at a state is the state's own value
/// for each named variable. The walk is structural over the named measure
/// and consults no ambient fact: it is the exact reading of the declared
/// measure at that state, which is what makes the back-edge bundle member
/// and the declared clause the same object.
pub(super) fn c_ranking_measure_term(
    expression: &CExpression,
    state: &CState,
) -> Result<Bitvector32Term, String> {
    // The declared measure is read as one affine form over the state's own
    // values. Folding it keeps `n - (i + 1)` from carrying an intermediate
    // `i + 1` whose definedness would need a bound the measure never claims,
    // and makes the member a stable function of the declaration rather than
    // of the assignment order that produced the state.
    c_ranking_measure_term_unfolded(expression, state).map(|term| canonical_ranking_term(&term))
}

fn c_ranking_measure_term_unfolded(
    expression: &CExpression,
    state: &CState,
) -> Result<Bitvector32Term, String> {
    use CExpression::*;
    let binary = |left: &CExpression,
                  right: &CExpression,
                  operation: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term|
     -> Result<Bitvector32Term, String> {
        Ok(operation(
            c_ranking_measure_term_unfolded(left, state)?,
            c_ranking_measure_term_unfolded(right, state)?,
        ))
    };
    match expression {
        Value(CValue::Int32(value)) | Value(CValue::UInt8(value)) => Ok(value.clone()),
        Value(_) => Err("termination measures must be int32 expressions".into()),
        Variable(name) => match state.locals().get(name) {
            Some(CValue::Int32(value)) | Some(CValue::UInt8(value)) => Ok(value.clone()),
            Some(_) => Err(format!(
                "termination measure variable `{name}` does not hold an int32 value"
            )),
            None => Err(format!(
                "termination measure references unknown variable `{name}`"
            )),
        },
        Cast {
            expression,
            target_type: CType::Int32 | CType::UInt8,
            ..
        } => c_ranking_measure_term_unfolded(expression, state),
        Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            let (condition, value) = c_ranking_measure_condition_term(condition, state)?;
            let then_term = c_ranking_measure_term_unfolded(then_branch, state)?;
            let else_term = c_ranking_measure_term_unfolded(else_branch, state)?;
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
        BitwiseNot(value) => Ok(Bitvector32Term::bitwise_not(
            c_ranking_measure_term_unfolded(value, state)?,
        )),
        Cast { .. }
        | FloatNegate(_)
        | FloatClassification { .. }
        | FunctionAddress(_)
        | AddressOf(_)
        | PointerOffsetBytes { .. }
        | Load(_)
        | TypedLoad { .. }
        | Index(_, _) => {
            Err("termination measures may only use scalar int32 expressions".into())
        }
        LessThan(_, _)
        | LessEqual(_, _)
        | GreaterThan(_, _)
        | GreaterEqual(_, _)
        | Equal(_, _)
        | NotEqual(_, _)
        | Not(_)
        | And(_, _)
        | Or(_, _) => Err("termination measures must have an int32 value".into()),
    }
}

fn c_ranking_measure_condition_term(
    expression: &CExpression,
    state: &CState,
) -> Result<(ConditionTerm, bool), String> {
    use CExpression::*;
    let binary = |left: &CExpression,
                  right: &CExpression,
                  operation: fn(Bitvector32Term, Bitvector32Term) -> ConditionTerm|
     -> Result<(ConditionTerm, bool), String> {
        Ok((
            operation(
                c_ranking_measure_term_unfolded(left, state)?,
                c_ranking_measure_term_unfolded(right, state)?,
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
            let (condition, value) = c_ranking_measure_condition_term(inner, state)?;
            Ok((condition, !value))
        }
        And(_, _) | Or(_, _) => Err(
            "compound boolean conditions are not atomic ranking measure conditions".into(),
        ),
        _ => Ok((
            ConditionTerm::equal(
                c_ranking_measure_term_unfolded(expression, state)?,
                Bitvector32Term::Constant(0),
            ),
            false,
        )),
    }
}

/// The display form of one `decreases` component, for bundle member contexts.
pub(super) fn c_ranking_measure_display(measure: &CExpression) -> String {
    termination_measure_display(measure)
}

/// The display form of a whole `decreases` clause.
pub(super) fn c_ranking_measures_display(measures: &[CExpression]) -> String {
    termination_measures_display(measures)
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

/// The declared `decreases` measure each verified loop rule certified.
///
/// A rule's loop head carries the measure whose back-edge members its bundle
/// closed. Matching the rule to the source loop by index and executable shape
/// is what binds that certification to this function's loop.
fn verified_loop_ranking_measures(
    function_name: &str,
    source_body: &CStatement,
    rules: &[CVerifiedLoopRule],
) -> Result<BTreeMap<usize, Vec<CExpression>>, CTerminationError> {
    let mut certified: BTreeMap<usize, Vec<CExpression>> = BTreeMap::new();
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
            ranking_measures, ..
        } = &rule.loop_statement
        else {
            return Err(error(format!(
                "verified loop rule for `{function_name}` is not a while loop"
            )));
        };
        if ranking_measures.is_empty() {
            continue;
        }
        if let Some(existing) = certified.get(&index) {
            if existing != ranking_measures {
                return Err(error(format!(
                    "verified loop rules for `{function_name}` disagree on loop {index} `decreases`"
                )));
            }
        } else {
            certified.insert(index, ranking_measures.clone());
        }
    }
    Ok(certified)
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

/// Confirms that every loop the plan ranks has a checked back-edge bundle
/// for exactly that measure, and reports whether every loop in the statement
/// is ranked at all.
///
/// This pass proves nothing. A loop's nonnegativity and lexicographic
/// decrease obligations are members of its `close_invariants` bundle, which
/// the loop's own verified rule already certified; the rule carries the
/// declared measure on its loop head, so matching it against the plan is the
/// whole of the check here.
fn check_loops(
    statement: &CStatement,
    supplied: &BTreeMap<usize, Vec<CExpression>>,
    certified: &BTreeMap<usize, Vec<CExpression>>,
    function_name: &str,
    next_index: &mut usize,
) -> Result<bool, CTerminationError> {
    match statement {
        CStatement::Seq(first, second) => Ok(check_loops(
            first,
            supplied,
            certified,
            function_name,
            next_index,
        )? && check_loops(
            second,
            supplied,
            certified,
            function_name,
            next_index,
        )?),
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => Ok(check_loops(
            then_branch,
            supplied,
            certified,
            function_name,
            next_index,
        )? && check_loops(
            else_branch,
            supplied,
            certified,
            function_name,
            next_index,
        )?),
        CStatement::While { body, .. } => {
            let index = *next_index;
            *next_index += 1;
            let nested_terminate =
                check_loops(body, supplied, certified, function_name, next_index)?;
            let Some(measures) = supplied.get(&index) else {
                return Ok(false);
            };
            if measures.is_empty() {
                return Err(error(format!(
                    "loop {index} has an empty termination measure"
                )));
            }
            match certified.get(&index) {
                Some(checked) if checked == measures => Ok(nested_terminate),
                Some(checked) => Err(error(format!(
                    "loop {index} in `{function_name}` was certified for `{}`, not the planned `{}`",
                    termination_measures_display(checked),
                    termination_measures_display(measures)
                ))),
                None => Err(error(format!(
                    "loop {index} in `{function_name}` has no verified loop rule carrying its \
                     `decreases` measure, so its back-edge ranking obligations were never checked"
                ))),
            }
        }
        CStatement::Switch { cases, .. } => {
            let mut nested_terminate = true;
            for case in cases {
                nested_terminate &=
                    check_loops(&case.body, supplied, certified, function_name, next_index)?;
            }
            Ok(nested_terminate)
        }
        CStatement::ContinueWithStep { step } => {
            check_loops(step, supplied, certified, function_name, next_index)
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
        | CStatement::CopyAggregate { .. }
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
            // A callee spelled like an object this function binds is a call
            // through that object: C11 6.2.1p4 hides a file-scope function of
            // the same name behind the parameter or local. Resolving it to the
            // function would hand the call that function's ranking proof, so
            // record it under a spelling no function can have and leave it
            // unranked, which is the treatment every indirect call gets.
            let objects = function_object_names(function);
            let found = found
                .into_iter()
                .map(|callee| {
                    if objects.contains(&callee) {
                        format!("{callee}#indirect")
                    } else {
                        callee
                    }
                })
                .collect::<BTreeSet<_>>();
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
            let certified = match verified_loop_rules.get(name) {
                Some(rules) => verified_loop_ranking_measures(name, &function.source_body, rules)?,
                None => BTreeMap::new(),
            };
            let mut next_loop = 0;
            component_ok &= check_loops(
                &function.source_body,
                loop_measures,
                &certified,
                name,
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
                        &measure,
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
            ranking_measures: Vec::new(),
            condition: variable("c"),
            invariant: Vec::new(),
            invariant_checks: Vec::new(),
            effect_checks: Vec::new(),
            resource_specs: Vec::new(),
            do_while: false,
            body: Box::new(branch),
        };
        assert!(statement_takes_address_of(&body, "n"));
        assert!(!statement_takes_address_of(&body, "c"));
    }
}

#[cfg(test)]
mod ranking_member_tests {
    use super::*;

    fn scalar_state(bindings: &[(&str, Bitvector32Term)]) -> CState {
        let mut state = CState::new();
        for (name, value) in bindings {
            state.locals.set_typed(
                (*name).to_string(),
                CValue::Int32(value.clone()),
                CType::Int32,
            );
        }
        state
    }

    /// Bundle membership is a fixed function of the declaration: one
    /// nonnegativity obligation per component in declaration order, then one
    /// decrease obligation that is the right-nested disjunction over pivots.
    /// A retained certificate is only stable across runs and sites because
    /// this order never depends on the state or the ambient facts.
    #[test]
    fn ranking_members_are_ordered_and_right_nested() {
        let outer = Bitvector32Term::Variable(Variable(1));
        let inner = Bitvector32Term::Variable(Variable(2));
        let entry = scalar_state(&[("i", outer.clone()), ("j", inner.clone())]);
        let post_outer = Bitvector32Term::subtract(outer.clone(), Bitvector32Term::Constant(1));
        let post_inner = Bitvector32Term::add(inner.clone(), Bitvector32Term::Constant(1));
        let back_edge = scalar_state(&[("i", post_outer.clone()), ("j", post_inner.clone())]);
        let measures = vec![
            CExpression::Variable("i".to_string()),
            CExpression::Variable("j".to_string()),
        ];
        let obligations = collect_loop_ranking_obligations(&back_edge, &entry, &measures)
            .expect("scalar measures read at both ends");
        assert_eq!(obligations.len(), 3);

        for (obligation, (component, post)) in obligations
            .iter()
            .zip([("i", post_outer.clone()), ("j", post_inner.clone())])
        {
            assert_eq!(
                obligation.proposition(),
                &Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), post),
                    true,
                )
            );
            assert!(
                obligation
                    .context()
                    .is_some_and(|context| context.contains(&format!("`{component}`"))),
                "member names its component: {:?}",
                obligation.context()
            );
        }

        let pivot_first = Proposition::ConditionIs(
            ConditionTerm::signed_less_than(post_outer.clone(), outer.clone()),
            true,
        );
        let pivot_second = Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(post_outer, outer),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(post_inner, inner),
                true,
            )),
        );
        assert_eq!(
            obligations[2].proposition(),
            &Proposition::Or(Box::new(pivot_first), Box::new(pivot_second))
        );
    }

    /// A single component takes the bare strict decrease, with no disjunction
    /// and no equality prefix to choose between.
    #[test]
    fn one_component_takes_a_bare_decrease_member() {
        let value = Bitvector32Term::Variable(Variable(7));
        let entry = scalar_state(&[("n", value.clone())]);
        let post = Bitvector32Term::subtract(value.clone(), Bitvector32Term::Constant(1));
        let back_edge = scalar_state(&[("n", post.clone())]);
        let measures = vec![CExpression::Variable("n".to_string())];
        let obligations = collect_loop_ranking_obligations(&back_edge, &entry, &measures)
            .expect("a scalar measure reads at both ends");
        assert_eq!(obligations.len(), 2);
        assert_eq!(
            obligations[1].proposition(),
            &Proposition::ConditionIs(ConditionTerm::signed_less_than(post, value), true)
        );
    }

    /// The structural-path helper has no proof site to emit an undischarged
    /// obligation to, so it settles one only by an exact route. A disjunction
    /// with one available arm is exactly the shape the deleted general prover
    /// used to accept here by selecting the arm.
    #[test]
    fn structural_path_refuses_an_obligation_no_exact_route_settles() {
        let left = Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(0),
                Bitvector32Term::Variable(Variable(1)),
            ),
            true,
        );
        let right = Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(0),
                Bitvector32Term::Variable(Variable(2)),
            ),
            true,
        );
        let mut assumptions = PureFactContext::new()
            .assume_proposition(left.clone())
            .assume_proposition(right.clone());
        let disjunction = Proposition::Or(Box::new(left), Box::new(right));
        assert!(
            assume_structural_path(
                &mut assumptions,
                &[],
                &[ProofObligation::verification_condition(disjunction.clone())],
            )
            .is_none(),
            "an arm choice is not an exact route, so the path is refused"
        );
        let mut exact = PureFactContext::new().assume_proposition(disjunction.clone());
        assert!(
            assume_structural_path(
                &mut exact,
                &[],
                &[ProofObligation::verification_condition(disjunction)],
            )
            .is_some(),
            "the exact fact still settles its own obligation"
        );
    }
}
