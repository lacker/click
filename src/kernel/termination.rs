use super::prelude::*;

/// Charges `units` of termination work to the ambient deterministic-work
/// counters.
///
/// The termination check has no tactic of its own, so this is measurement
/// only: it never consumes a budget and so cannot change a verdict. Every
/// unit is one step the algorithm actually takes — a statement of a body it
/// walks, a call edge it reads, a level member it settles, a planner visit,
/// or a worklist step — so `termination_scaling_tests` counts the checker
/// rather than the host clock.
fn charge_termination_work(units: usize) {
    crate::instrumentation::record_deterministic_work(units);
}

/// The one library call the execution model implements itself instead of
/// looking up a function; see `c0_statement_calls`.
const MODELED_REALLOC: &str = "realloc";

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
            pointee_struct,
            pointee_volatile,
            pointee_constant,
        } => Cast {
            expression: unary(body),
            target_type: *target_type,
            pointee_struct: pointee_struct.clone(),
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
            source,
        } => TypedLoad {
            pointer: unary(pointer),
            value_type: *value_type,
            volatile: *volatile,
            source: source.clone(),
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
    /// One entry per body the definition can take. An `if`-guarded body is
    /// the single arm, guarded by the definition's own condition; a
    /// `match model` body contributes one arm per matched variant whose own
    /// facts separate it from every other variant (gap 7).
    arms: Vec<StructuralResourceArm>,
}

/// One body of the measured definition, with the conditions that select it
/// and the direct recursive children it names.
struct StructuralResourceArm {
    /// Any one of these, established on the path, selects this arm. They are
    /// instantiated at the measure's arguments, so they are conditions about
    /// this call's own C expressions.
    guards: Vec<CExpression>,
    /// Whether the function's own `requires` already establishes a guard, so
    /// every path into the body starts inside this arm.
    guard_is_precondition: bool,
    children: Vec<Vec<CExpression>>,
    /// Direct recursive children named through a `let` witness of the
    /// definition rather than a C expression of its parameters.
    witness_children: Vec<WitnessChildMeasure>,
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
    // An arm is active on this path when the path establishes one of the
    // conditions that selects it, or when the function's own requirements
    // already did. Cost is the arm's own guards, not a search.
    let active = measure
        .arms
        .iter()
        .filter(|arm| {
            arm.guard_is_precondition
                || arm.guards.iter().any(|guard| {
                    path.conditions.iter().any(|(condition, value)| {
                        branch_establishes_structural_guard(condition, *value, guard)
                    })
                })
        })
        .collect::<Vec<_>>();
    if active.is_empty() {
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
    if !active.iter().any(|arm| {
        arm.children.contains(&call_measure_arguments)
            || call_passes_witness_child(function, measure, arm, &call_measure_arguments)
    }) {
        return Err(error(format!(
            "recursive call to `{function_name}` does not pass a direct contained child of its structural resource measure"
        )));
    }
    Ok(())
}

/// The resource-measure walk: one path per way of reaching a statement,
/// carrying the branch conditions that got there and the aliases the
/// assignments established. A recursive call is checked once per path, so a
/// path the walk stops following is a recursive call nothing checks — which is
/// why this shares [`walk_termination_paths`] with the `int32` measure's walk
/// rather than spelling the control flow a second time.
struct StructuralMeasureWalk<'a> {
    function: &'a CFunction,
    measure: &'a StructuralResourceMeasure,
}

impl TerminationWalk for StructuralMeasureWalk<'_> {
    type Path = StructuralRecursionPath;

    fn step(
        &self,
        statement: &CStatement,
        paths: Vec<Self::Path>,
    ) -> Result<Vec<Self::Path>, CTerminationError> {
        let forget = |name: &str, paths: Vec<Self::Path>| {
            paths
                .into_iter()
                .map(|mut path| {
                    path.aliases.remove(name);
                    path
                })
                .collect()
        };
        match statement {
            CStatement::Skip
            | CStatement::Continue
            | CStatement::Goto { .. }
            | CStatement::Assert { .. }
            | CStatement::HeapFree { .. }
            | CStatement::Store { .. }
            | CStatement::TypedStore { .. }
            | CStatement::CopyAggregate { .. }
            | CStatement::Update { .. } => Ok(paths),
            CStatement::Declare { name, .. } | CStatement::DeclareAggregate { name, .. } => {
                Ok(forget(name, paths))
            }
            CStatement::HeapAllocate { target, .. } => Ok(forget(target, paths)),
            CStatement::Assign { name, expression } => Ok(paths
                .into_iter()
                .map(|mut path| {
                    let expression = resolve_c_expression_aliases(expression, &path.aliases);
                    path.aliases.insert(name.clone(), expression);
                    path
                })
                .collect()),
            CStatement::CallAssign {
                target,
                function_name,
                arguments,
            } => {
                for path in &paths {
                    check_structural_recursive_call(
                        function_name,
                        arguments,
                        self.function,
                        self.measure,
                        path,
                    )?;
                }
                Ok(forget(target, paths))
            }
            CStatement::Call {
                function_name,
                arguments,
            } => {
                for path in &paths {
                    check_structural_recursive_call(
                        function_name,
                        arguments,
                        self.function,
                        self.measure,
                        path,
                    )?;
                }
                Ok(paths)
            }
            statement => unreachable!("control flow is the skeleton's: {statement:?}"),
        }
    }

    fn refine(
        &self,
        condition: &CExpression,
        taken: bool,
        paths: Vec<Self::Path>,
    ) -> Vec<Self::Path> {
        paths
            .into_iter()
            .map(|mut path| {
                let condition = resolve_c_expression_aliases(condition, &path.aliases);
                path.conditions.push((condition, taken));
                path
            })
            .collect()
    }

    fn unbind(&self, binding: &str, paths: Vec<Self::Path>) -> Vec<Self::Path> {
        paths
            .into_iter()
            .map(|mut path| {
                path.aliases.remove(binding);
                path
            })
            .collect()
    }
}

fn structural_recursion_paths(
    statement: &CStatement,
    function: &CFunction,
    measure: &StructuralResourceMeasure,
    paths: Vec<StructuralRecursionPath>,
) -> Result<Vec<StructuralRecursionPath>, CTerminationError> {
    Ok(walk_termination_paths(
        &StructuralMeasureWalk { function, measure },
        statement,
        paths,
    )?
    .continuing)
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
    arm: &StructuralResourceArm,
    call_measure_arguments: &[CExpression],
) -> bool {
    const PARAMETER_VARIABLE_BASE: u64 = 4_200_000_000;
    const WITNESS_VARIABLE_BASE: u64 = 4_250_000_000;
    if arm.witness_children.is_empty() {
        return false;
    }
    let mut budget = ExecutionBudget::for_new_execution();
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
    'children: for child in &arm.witness_children {
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

/// The bodies and direct recursive children of a measured entry resource.
///
/// An `if`-guarded body is one arm selected by the definition's own condition.
/// A `match model` body (gap 7) contributes one arm per matched variant: its
/// named and unnamed children of the same family are the arm's structural
/// children, and the arm is selected by a fact of its own that every other
/// variant's facts explicitly deny. That denial is what makes the guard an
/// arm selection rather than an unrelated condition, and it is the syntactic
/// form of the same decision `select_resource_model_arm` makes from premises
/// at a loop head.
///
/// Work is the definition's own clauses: each arm's facts are compared only
/// with the other arms' facts of this one definition.
fn structural_resource_children(
    function: &CFunction,
    requirement_index: usize,
) -> Result<StructuralResourceMeasure, CTerminationError> {
    let Some(resource) = function.resource_requires().get(requirement_index) else {
        return Err(error(format!(
            "structural resource measure index is invalid for `{}`",
            function.name()
        )));
    };
    // `owns t: tree_at(root);` measures the instance the binder names, so the
    // measured family is the instance spec's own resource.
    let term = resource
        .term()
        .instance_resource()
        .unwrap_or_else(|| resource.term());
    let (Some(name), Some(arguments)) = (term.declared_name(), term.declared_arguments()) else {
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
    // A matched definition carries its children inside its arms. The
    // definition-level flag counts those too, but the arm walk below gives the
    // better message ("no direct recursive child") for a matched body, so keep
    // this early refusal for the unmatched shape.
    if definition.matched.is_none() && !definition.is_recursive() {
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
    let mentions_witness = |expression: &CExpression| {
        definition
            .witnesses()
            .iter()
            .any(|witness| c_expression_mentions_variable(expression, witness.name()))
    };
    let mentions_binding = |expression: &CExpression, bound: &BTreeSet<String>| {
        bound
            .iter()
            .any(|binding| c_expression_mentions_variable(expression, binding))
    };
    let structural_children = |contained: &[CResourceSpec],
                               bound: &BTreeSet<String>|
     -> (Vec<Vec<CExpression>>, Vec<WitnessChildMeasure>) {
        let mut children = Vec::new();
        let mut witness_children = Vec::new();
        for spec in contained {
            let (Some(child_name), Some(child_arguments)) =
                (spec.declared_name(), spec.declared_arguments())
            else {
                continue;
            };
            if child_name != name {
                continue;
            }
            if child_arguments
                .iter()
                .any(|argument| mentions_binding(argument, bound))
            {
                continue;
            }
            if child_arguments.iter().any(mentions_witness) {
                witness_children.push(WitnessChildMeasure {
                    definition: definition.clone(),
                    arguments: child_arguments.to_vec(),
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
        (children, witness_children)
    };
    let mut arms = Vec::new();
    if let Some(body) = definition.matched.as_ref() {
        for (index, arm) in body.arms.iter().enumerate() {
            let bound = arm.bindings.iter().cloned().collect::<BTreeSet<_>>();
            let (mut children, witness_children) = structural_children(&arm.contains, &bound);
            for child in &arm.children {
                if child.resource != name {
                    continue;
                }
                if child.arguments.iter().any(|argument| {
                    mentions_binding(argument, &bound) || mentions_witness(argument)
                }) {
                    continue;
                }
                children.push(
                    child
                        .arguments
                        .iter()
                        .map(|argument| substitute_c_expression_variables(argument, &substitutions))
                        .collect::<Vec<_>>(),
                );
            }
            if children.is_empty() && witness_children.is_empty() {
                continue;
            }
            // A fact of this arm selects it only when every other arm denies
            // that same fact. `fact p != 0` in a `Node` arm selects it because
            // the `Empty` arm states `fact p == 0`.
            let mut guards = Vec::new();
            let mut guard_is_precondition = false;
            for fact in &arm.facts {
                let Some(instantiated) = instantiate_structural_guard(fact, &substitutions) else {
                    continue;
                };
                let Some(guard) = structural_guard_expression(&instantiated) else {
                    continue;
                };
                if mentions_binding(&guard, &bound) || mentions_witness(&guard) {
                    continue;
                }
                let denied_elsewhere = body.arms.iter().enumerate().all(|(other, candidate)| {
                    other == index
                        || candidate.facts.iter().any(|other_fact| {
                            instantiate_structural_guard(other_fact, &substitutions)
                                .as_ref()
                                .and_then(structural_guard_expression)
                                .is_some_and(|other_guard| {
                                    branch_establishes_structural_guard(&other_guard, false, &guard)
                                })
                        })
                });
                if !denied_elsewhere {
                    continue;
                }
                if function.contract_requires().contains(&instantiated) {
                    guard_is_precondition = true;
                }
                guards.push(guard);
            }
            if guards.is_empty() {
                return Err(error(format!(
                    "resource measure `{name}` arm `{}` names children but no fact of its own that the other arms deny, so no condition selects it",
                    arm.variant
                )));
            }
            arms.push(StructuralResourceArm {
                guards,
                guard_is_precondition,
                children,
                witness_children,
            });
        }
    } else {
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
        let (children, witness_children) =
            structural_children(definition.contains(), &BTreeSet::new());
        if !children.is_empty() || !witness_children.is_empty() {
            arms.push(StructuralResourceArm {
                guards: vec![guard],
                guard_is_precondition,
                children,
                witness_children,
            });
        }
    }
    if arms.is_empty() {
        return Err(error(format!(
            "resource measure `{name}` has no direct recursive child"
        )));
    }
    Ok(StructuralResourceMeasure {
        arguments: arguments.to_vec(),
        arms,
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
    charge_termination_work(1);
    let escapes = |expression: &CExpression| expression_takes_address_of(expression, name);
    match statement {
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. } => false,
        CStatement::ForStep { step, .. } => statement_takes_address_of(step, name),
        CStatement::Assign { expression, .. }
        | CStatement::Return(expression)
        | CStatement::Throw(expression) => escapes(expression),
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
        CStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            statement_takes_address_of(try_body, name) || statement_takes_address_of(handler, name)
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
    measures: &[CRankingComponent],
    body: &CStatement,
) -> Result<(), String> {
    for measure in measures {
        reject_address_escaped_ranking_component(function_name, measure, body)
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

/// The same check for one certified `decreases` component.
///
/// A measure names a local's *value*, so a local whose address escapes is not
/// one the measure can read; that is what the C form already refuses. A pure
/// component reaches the same locals through its lowered C fragments, so the
/// names it reads are collected from the lowered expression. A lowered form
/// this collection does not cover is refused outright rather than passed
/// unchecked: the escape check is the kernel's, not the surface's.
fn reject_address_escaped_ranking_component(
    function_name: &str,
    component: &CRankingComponent,
    body: &CStatement,
) -> Result<(), CTerminationError> {
    match component {
        CRankingComponent::CExpression(expression) => {
            reject_address_escaped_expression_measure(function_name, expression, body)
        }
        CRankingComponent::Pure { source, expression } => {
            let mut variables = BTreeSet::new();
            if !collect_spec_expression_c_variables(expression, &mut variables) {
                return Err(error(format!(
                    "the `decreases` component `{source}` in `{function_name}` uses a \
                     specification form whose C variables cannot be collected, so it cannot be \
                     checked against address-escaped locals"
                )));
            }
            for variable in variables {
                reject_address_escaped_measure(function_name, &variable, body)?;
            }
            Ok(())
        }
        CRankingComponent::PureInteger { source, expression } => {
            let mut variables = BTreeSet::new();
            if !collect_spec_integer_expression_c_variables(expression, &mut variables) {
                return Err(error(format!(
                    "the `decreases` component `{source}` in `{function_name}` uses a \
                     specification form whose C variables cannot be collected, so it cannot be \
                     checked against address-escaped locals"
                )));
            }
            for variable in variables {
                reject_address_escaped_measure(function_name, &variable, body)?;
            }
            Ok(())
        }
    }
}

/// The same collection for a lowered Integer specification expression.
///
/// A kernel `IntegerTerm` names no source local: a local a measure reads
/// reaches the Integer carrier through `FromMachine`, or as a pure
/// application's machine argument, and both are walked here. That is why
/// `Term` contributes no name rather than refusing, exactly as
/// `SpecExpression::Value` does in the machine carrier.
fn collect_spec_integer_expression_c_variables(
    expression: &SpecIntegerExpression,
    names: &mut BTreeSet<String>,
) -> bool {
    charge_termination_work(1);
    let both = |left: &SpecIntegerExpression,
                right: &SpecIntegerExpression,
                names: &mut BTreeSet<String>| {
        collect_spec_integer_expression_c_variables(left, names)
            && collect_spec_integer_expression_c_variables(right, names)
    };
    match expression {
        SpecIntegerExpression::Term(_) => true,
        // A resource field reads the binder's instance, not a C local.
        SpecIntegerExpression::ResourceField(_) => true,
        SpecIntegerExpression::FromMachine(value) => {
            collect_spec_expression_c_variables(value, names)
        }
        SpecIntegerExpression::Negate(inner) => {
            collect_spec_integer_expression_c_variables(inner, names)
        }
        SpecIntegerExpression::Add(left, right)
        | SpecIntegerExpression::Subtract(left, right)
        | SpecIntegerExpression::Multiply(left, right) => both(left, right, names),
        SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
            arguments.iter().all(|argument| match argument {
                SpecPureFunctionArgument::Value(value) => {
                    collect_spec_expression_c_variables(value, names)
                }
                SpecPureFunctionArgument::ArrayRef { pointer, .. } => {
                    collect_spec_expression_c_variables(pointer, names)
                }
                SpecPureFunctionArgument::Integer(value) => {
                    collect_spec_integer_expression_c_variables(value, names)
                }
                SpecPureFunctionArgument::Algebraic(_) => false,
            })
        }
        SpecIntegerExpression::AlgebraicMatch { .. } | SpecIntegerExpression::RangeFold { .. } => {
            false
        }
    }
}

/// Collects the C locals one lowered specification expression reads, or
/// reports that it contains a form this collection does not cover.
///
/// Work is linear in the expression, which is the declared component; nothing
/// ambient is scanned.
fn collect_spec_expression_c_variables(
    expression: &SpecExpression,
    names: &mut BTreeSet<String>,
) -> bool {
    charge_termination_work(1);
    let both = |left: &SpecExpression, right: &SpecExpression, names: &mut BTreeSet<String>| {
        collect_spec_expression_c_variables(left, names)
            && collect_spec_expression_c_variables(right, names)
    };
    match expression {
        SpecExpression::Value(_) => true,
        SpecExpression::CExpression(expression) => {
            collect_c_expression_variables(expression, names);
            true
        }
        SpecExpression::Add(left, right)
        | SpecExpression::Subtract(left, right)
        | SpecExpression::Multiply(left, right)
        | SpecExpression::Divide(left, right)
        | SpecExpression::Remainder(left, right)
        | SpecExpression::ShiftLeft(left, right)
        | SpecExpression::ShiftRight(left, right)
        | SpecExpression::BitwiseAnd(left, right)
        | SpecExpression::BitwiseOr(left, right)
        | SpecExpression::BitwiseXor(left, right) => both(left, right, names),
        SpecExpression::BitwiseNot(value) | SpecExpression::Cast(value, _) => {
            collect_spec_expression_c_variables(value, names)
        }
        SpecExpression::PointerOffset {
            pointer, elements, ..
        } => both(pointer, elements, names),
        SpecExpression::MemoryLoad { pointer, .. } => {
            collect_spec_expression_c_variables(pointer, names)
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => {
            arguments.iter().all(|argument| match argument {
                SpecPureFunctionArgument::Value(value) => {
                    collect_spec_expression_c_variables(value, names)
                }
                SpecPureFunctionArgument::ArrayRef { pointer, .. } => {
                    collect_spec_expression_c_variables(pointer, names)
                }
                SpecPureFunctionArgument::Integer(_) | SpecPureFunctionArgument::Algebraic(_) => {
                    false
                }
            })
        }
        // A resource field reads the binder's instance, not a C local.
        SpecExpression::ResourceField { .. } => true,
        SpecExpression::IntegerToMachine { .. }
        | SpecExpression::AlgebraicMatch { .. }
        | SpecExpression::CountedResourceCount { .. }
        | SpecExpression::If { .. }
        | SpecExpression::RangeFold { .. }
        | SpecExpression::Let { .. }
        | SpecExpression::LoopEntrySnapshot(_) => false,
    }
}

fn statement_calls(statement: &CStatement, calls: &mut BTreeSet<String>) {
    charge_termination_work(1);
    match statement {
        CStatement::CallAssign { function_name, .. } | CStatement::Call { function_name, .. } => {
            calls.insert(function_name.clone());
        }
        CStatement::Seq(first, second) => {
            statement_calls(first, calls);
            statement_calls(second, calls);
        }
        CStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            statement_calls(try_body, calls);
            statement_calls(handler, calls);
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
        CStatement::ForStep { step, .. } => statement_calls(step, calls),
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assign { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Throw(_)
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
    charge_termination_work(1);
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
        CStatement::TryCatchInt32 {
            try_body,
            binding,
            handler,
            ..
        } => {
            statement_declared_variables(try_body, names);
            names.insert(binding.clone());
            statement_declared_variables(handler, names);
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
        CStatement::ForStep { step, .. } => statement_declared_variables(step, names),
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Assign { .. }
        | CStatement::Update { .. }
        | CStatement::Call { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Throw(_)
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

/// The paths that continue past a join, as one bound.
///
/// A recursive edge is checked against every path's lower bound on the
/// measure, so only the weakest of them decides; and a branch refines a
/// bound as the larger of the bound and what its condition says, which is
/// monotone, so refining the weakest bound gives the weakest refined bound.
/// Keeping one bound per join is therefore exactly as strict as keeping
/// every path's, and keeps the list from doubling at each sequential `if`.
/// No path continuing, after a `return` on every path, stays the empty list.
fn weakest_lower_bound(paths: Vec<i64>) -> Vec<i64> {
    paths.into_iter().min().into_iter().collect()
}

/// Where the paths leaving a statement go.
///
/// `continuing` are the paths that fall out of this statement into the next
/// one. `broken` are the paths that left the innermost enclosing `switch` or
/// loop through a `break`: they do not reach the statement after this one,
/// they resume after that construct, and putting them back is that
/// construct's job.
///
/// The split exists because neither measure form has a verification condition
/// behind it — the walk *is* the proof of descent — so a path the walk stops
/// following is a recursive call nothing checks. `break` used to answer the
/// empty list, which is right for a loop body, where the loop discards its
/// body's answer anyway, and wrong for a `switch`, where it is the ordinary
/// way a case ends. An empty list then propagates: `Seq` keeps it empty, and
/// `If` and `While` iterate over it, so every later branch and loop body in
/// the function went unwalked.
struct WalkPaths<P> {
    continuing: Vec<P>,
    broken: Vec<P>,
}

impl<P> WalkPaths<P> {
    fn continuing(paths: Vec<P>) -> Self {
        Self {
            continuing: paths,
            broken: Vec::new(),
        }
    }

    fn none() -> Self {
        Self {
            continuing: Vec::new(),
            broken: Vec::new(),
        }
    }
}

/// The half of a termination walk that a measure form owns: what its paths
/// are, what a straight-line statement does to them, and what a branch
/// condition says about them. The other half — which statements a path
/// reaches at all — is [`walk_termination_paths`], and it is shared.
///
/// It is shared because the two forms disagreeing about that is a soundness
/// bug rather than an inconsistency. `4ab4c50a` fixed `switch` and `break` in
/// the `int32` form and recorded that the resource form beside it had the same
/// `switch` shape and the opposite `break`; the resource form was still
/// admitting `spin(1)` calling `spin(1)` afterwards, over `decreases
/// zero_list(node)` rather than `decreases n`. One skeleton, so a third form
/// cannot re-derive the same mistake.
trait TerminationWalk {
    type Path: Clone;

    /// A statement that is not control flow: the measure form's own checks,
    /// and whatever bookkeeping its paths carry. The control-flow variants
    /// never reach it.
    fn step(
        &self,
        statement: &CStatement,
        paths: Vec<Self::Path>,
    ) -> Result<Vec<Self::Path>, CTerminationError>;

    /// The paths entering a branch arm or a loop body, refined by the
    /// condition that selects it.
    fn refine(
        &self,
        condition: &CExpression,
        taken: bool,
        paths: Vec<Self::Path>,
    ) -> Vec<Self::Path>;

    /// Drops a binding a `try`/`catch` handler does not see.
    fn unbind(&self, binding: &str, paths: Vec<Self::Path>) -> Vec<Self::Path>;

    /// The paths that continue past a join, as the form prefers to hold them.
    /// Narrowing here must keep every refusal the unnarrowed list would make.
    fn join(&self, paths: Vec<Self::Path>) -> Vec<Self::Path> {
        paths
    }
}

/// The control-flow skeleton both termination measure forms walk.
///
/// A branch arm, a loop body, and a case body are entered even where no path
/// reaches them: the walk is the whole proof, so a subtree it never enters is
/// a recursive call nothing checks, and entering with an empty path list adds
/// the refusals that do not compare against a path and no others.
fn walk_termination_paths<W: TerminationWalk>(
    walk: &W,
    statement: &CStatement,
    paths: Vec<W::Path>,
) -> Result<WalkPaths<W::Path>, CTerminationError> {
    let descend = |statement: &CStatement, paths: Vec<W::Path>| {
        walk_termination_paths(walk, statement, paths)
    };
    match statement {
        CStatement::ForStep { step, .. } => descend(step, paths),
        CStatement::Return(_) | CStatement::Throw(_) => Ok(WalkPaths::none()),
        // A `break` leaves the innermost `switch` or loop and resumes after
        // it, carrying what it holds here. It does not reach the next
        // statement in this body, which is what `continuing` is empty for.
        CStatement::Break => Ok(WalkPaths {
            continuing: Vec::new(),
            broken: paths,
        }),
        CStatement::Seq(first, second) => {
            let first = descend(first, paths)?;
            let mut second = descend(second, first.continuing)?;
            second.broken.extend(first.broken);
            Ok(second)
        }
        CStatement::TryCatchInt32 {
            try_body,
            binding,
            handler,
            ..
        } => {
            let handler_paths = walk.unbind(binding, paths.clone());
            let try_body = descend(try_body, paths)?;
            let handler = descend(handler, handler_paths)?;
            let mut continuing = try_body.continuing;
            continuing.extend(handler.continuing);
            let mut broken = try_body.broken;
            broken.extend(handler.broken);
            Ok(WalkPaths {
                continuing: walk.join(continuing),
                broken: walk.join(broken),
            })
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut continuing = Vec::new();
            let mut broken = Vec::new();
            for (branch, taken) in [(then_branch, true), (else_branch, false)] {
                let arm = descend(branch, walk.refine(condition, taken, paths.clone()))?;
                continuing.extend(arm.continuing);
                broken.extend(arm.broken);
            }
            Ok(WalkPaths {
                continuing: walk.join(continuing),
                broken: walk.join(broken),
            })
        }
        CStatement::While {
            condition, body, ..
        } => {
            // A `break` in the body lands where the loop's own exit lands,
            // carrying what the incoming paths already carry, so it is
            // covered by the incoming paths this returns.
            descend(body, walk.refine(condition, true, paths.clone()))?;
            Ok(WalkPaths::continuing(paths))
        }
        CStatement::Switch { cases, .. } => {
            // Every way out of a `switch` continues at the statement after it:
            // a case body that ends normally (falling into the next case, and
            // out of the last one), a `break`, and — when no case matches and
            // there is no `default` — the selector path that runs no case body
            // at all. Each case body is entered with the incoming paths, which
            // carry less than anything a fall-through would, so they cover
            // fall-through too.
            let mut escaping = Vec::new();
            for case in cases {
                let case_paths = descend(&case.body, paths.clone())?;
                escaping.extend(case_paths.continuing);
                escaping.extend(case_paths.broken);
            }
            if cases.iter().all(|case| case.value.is_some()) {
                escaping.extend(paths);
            }
            Ok(WalkPaths {
                continuing: walk.join(escaping),
                broken: Vec::new(),
            })
        }
        statement => Ok(WalkPaths::continuing(walk.step(statement, paths)?)),
    }
}

/// The `int32`-parameter measure walk: one lower bound on the measure per way
/// of reaching a statement, checked against every recursive edge.
struct Int32MeasureWalk<'a> {
    measure: &'a str,
    component: &'a BTreeSet<String>,
    parameter_indices: &'a BTreeMap<String, usize>,
}

impl Int32MeasureWalk<'_> {
    fn check_recursive_call(
        &self,
        function_name: &str,
        arguments: &[CExpression],
        lower_bounds: &[i64],
    ) -> Result<(), CTerminationError> {
        if !self.component.contains(function_name) {
            return Ok(());
        }
        let measure = self.measure;
        let index = self.parameter_indices[function_name];
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
        Ok(())
    }
}

impl TerminationWalk for Int32MeasureWalk<'_> {
    type Path = i64;

    fn step(
        &self,
        statement: &CStatement,
        lower_bounds: Vec<i64>,
    ) -> Result<Vec<i64>, CTerminationError> {
        let measure = self.measure;
        match statement {
            CStatement::Skip
            | CStatement::Continue
            | CStatement::Goto { .. }
            | CStatement::Declare { .. }
            | CStatement::DeclareAggregate { .. }
            | CStatement::Assert { .. }
            | CStatement::HeapFree { .. }
            | CStatement::Store { .. }
            | CStatement::TypedStore { .. }
            | CStatement::CopyAggregate { .. } => Ok(lower_bounds),
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
                self.check_recursive_call(function_name, arguments, &lower_bounds)?;
                Ok(lower_bounds)
            }
            CStatement::Call {
                function_name,
                arguments,
            } => {
                self.check_recursive_call(function_name, arguments, &lower_bounds)?;
                Ok(lower_bounds)
            }
            statement => unreachable!("control flow is the skeleton's: {statement:?}"),
        }
    }

    fn refine(&self, condition: &CExpression, taken: bool, lower_bounds: Vec<i64>) -> Vec<i64> {
        lower_bounds
            .into_iter()
            .map(|bound| refined_lower_bound(condition, self.measure, taken, bound))
            .collect()
    }

    fn unbind(&self, _binding: &str, lower_bounds: Vec<i64>) -> Vec<i64> {
        lower_bounds
    }

    fn join(&self, lower_bounds: Vec<i64>) -> Vec<i64> {
        weakest_lower_bound(lower_bounds)
    }
}

fn recursion_paths(
    statement: &CStatement,
    measure: &str,
    component: &BTreeSet<String>,
    parameter_indices: &BTreeMap<String, usize>,
    lower_bounds: Vec<i64>,
) -> Result<Vec<i64>, CTerminationError> {
    let walk = Int32MeasureWalk {
        measure,
        component,
        parameter_indices,
    };
    Ok(walk_termination_paths(&walk, statement, lower_bounds)?.continuing)
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
        // The kernel expression no longer carries a field's name, so a read is
        // shown as the dereference it is, with its byte offset.
        TypedLoad { pointer, .. } | Load(pointer) => {
            format!("*({})", termination_measure_display(pointer))
        }
        PointerOffsetBytes { pointer, bytes } => {
            format!("{} + {bytes} bytes", termination_measure_display(pointer))
        }
        Index(base, index) => format!(
            "{}[{}]",
            termination_measure_display(base),
            termination_measure_display(index)
        ),
        Cast { expression, .. } => termination_measure_display(expression),
        _ => format!("{measure:?}"),
    }
}

/// What evaluating a measure's memory reads at one state left behind: the
/// facts the evaluator published and the obligations it could not discharge
/// itself, which are the reads' loadability.
#[derive(Default)]
pub(super) struct CRankingMeasureReads {
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

/// Where a measure's memory reads are evaluated. A measure over locals alone
/// needs none of it and is read from the state by itself.
pub(super) struct CRankingMeasureReader<'a> {
    pub(super) assumptions: &'a PureFactContext,
    pub(super) budget: &'a mut ExecutionBudget,
    pub(super) reads: CRankingMeasureReads,
}

/// The kernel term for one `decreases` component at one C state.
///
/// A ranking component is a scalar int32 or mathematical `Integer` expression,
/// so its value at a state
/// is a function of that state: the state's own value for each named local,
/// and, for a memory read, the value the expression evaluator gives that read
/// there. The arithmetic between them is read structurally and consults no
/// ambient fact, which is what makes the back-edge ranking obligation and the
/// declared clause the same object. A read goes through the evaluator because
/// an invariant about the same cell does, and the two must name the cell's
/// value by the same term for a proof to connect them.
///
/// A measure is never executed, so a read in it is not a C access: it names
/// the memory's content at that state. Its loadability is still returned as
/// an obligation, so the value a proof reasons about is one the program could
/// observe. A volatile read is refused, since it is not a function of state.
pub(super) fn c_ranking_measure_term(
    component: &CRankingComponent,
    state: &CState,
    reader: &mut CRankingMeasureReader<'_>,
) -> Result<CRankingMeasureValue, String> {
    match component {
        // The declared measure is read as one affine form over the state's
        // own values. Folding it keeps `n - (i + 1)` from carrying an
        // intermediate `i + 1` whose definedness would need a bound the
        // measure never claims, and makes the member a stable function of the
        // declaration rather than of the assignment order that produced the
        // state.
        CRankingComponent::CExpression(expression) => {
            c_ranking_measure_term_unfolded(expression, state, reader)
                .map(|term| CRankingMeasureValue::Machine(canonical_ranking_term(&term)))
        }
        CRankingComponent::Pure { expression, .. } => {
            pure_ranking_measure_term(expression, state, reader).map(CRankingMeasureValue::Machine)
        }
        CRankingComponent::PureInteger { expression, .. } => {
            pure_integer_ranking_measure_term(expression, state, reader)
                .map(CRankingMeasureValue::Integer)
        }
    }
}

/// `0 <= m` for one reading of a component, in that component's carrier.
pub(super) fn ranking_nonnegative_proposition(value: &CRankingMeasureValue) -> Proposition {
    Proposition::ConditionIs(
        match value {
            CRankingMeasureValue::Machine(term) => {
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), term.clone())
            }
            CRankingMeasureValue::Integer(term) => {
                ConditionTerm::integer_less_equal(IntegerTerm::constant_i64(0), term.clone())
            }
        },
        true,
    )
}

/// `post < pre` for the two readings of one component.
///
/// Both readings come from the same component, whose carrier is a function of
/// the declaration and not of the state, so the carriers always agree. A
/// disagreement is reported rather than coerced, because a comparison across
/// carriers would be a different relation than the one the declaration asked
/// for.
pub(super) fn ranking_decrease_proposition(
    post: &CRankingMeasureValue,
    pre: &CRankingMeasureValue,
    component: &CRankingComponent,
) -> Result<Proposition, String> {
    Ok(Proposition::ConditionIs(
        match (post, pre) {
            (CRankingMeasureValue::Machine(post), CRankingMeasureValue::Machine(pre)) => {
                ConditionTerm::signed_less_than(post.clone(), pre.clone())
            }
            (CRankingMeasureValue::Integer(post), CRankingMeasureValue::Integer(pre)) => {
                ConditionTerm::integer_less_than(post.clone(), pre.clone())
            }
            _ => return Err(mixed_ranking_carrier_message(component)),
        },
        true,
    ))
}

/// `post == pre`, the tie an outer lexicographic pivot stands on.
pub(super) fn ranking_tie_proposition(
    post: &CRankingMeasureValue,
    pre: &CRankingMeasureValue,
    component: &CRankingComponent,
) -> Result<Proposition, String> {
    Ok(Proposition::ConditionIs(
        match (post, pre) {
            (CRankingMeasureValue::Machine(post), CRankingMeasureValue::Machine(pre)) => {
                ConditionTerm::equal(post.clone(), pre.clone())
            }
            (CRankingMeasureValue::Integer(post), CRankingMeasureValue::Integer(pre)) => {
                ConditionTerm::integer_equal(post.clone(), pre.clone())
            }
            _ => return Err(mixed_ranking_carrier_message(component)),
        },
        true,
    ))
}

/// The component is rendered here rather than by the caller, so a tuple pays
/// for a display string only on the refusal path.
fn mixed_ranking_carrier_message(component: &CRankingComponent) -> String {
    format!(
        "the `decreases` component `{}` read as a machine int32 at one of the two states \
         and as a mathematical Integer at the other, so its two values cannot be ranked against \
         each other",
        c_ranking_measure_display(component)
    )
}

/// The kernel term for one pure Integer `decreases` component at one C state.
///
/// This is [`pure_ranking_measure_term`] in the other carrier: the same
/// evaluator a `requires` clause's Integer operand goes through, at this
/// state, under the same assumptions, with the reads' facts published and
/// their loadability kept. A state that splits the component into several
/// paths is refused rather than guessed, exactly as in the machine carrier.
fn pure_integer_ranking_measure_term(
    expression: &SpecIntegerExpression,
    state: &CState,
    reader: &mut CRankingMeasureReader<'_>,
) -> Result<IntegerTerm, String> {
    let paths = crate::kernel::spec::evaluate_spec_integer_measure_paths(
        state,
        expression,
        reader.assumptions,
        reader.budget,
    )
    .map_err(|error| format!("could not evaluate a termination measure: {error:?}"))?;
    let [path] = paths.as_slice() else {
        return Err(format!(
            "a termination measure must have exactly one value at this state; this one has {}",
            paths.len()
        ));
    };
    reader.reads.obligations.extend(path.obligations.clone());
    reader.reads.facts.extend(path.facts.clone());
    Ok(path.value.clone())
}

/// The kernel term for one pure `decreases` component at one C state.
///
/// The component is the same lowered specification expression a loop
/// invariant's expression is, so it is evaluated here by the same evaluator,
/// at this state, under the same assumptions. The caller evaluates the one
/// declared expression twice, once per state; nothing the surface supplies
/// names a state, so the two terms are the same function of two states.
///
/// A component that reads memory publishes the evaluator's facts and keeps
/// its unfulfilled obligations, which are the reads' loadability, exactly as
/// the C-expression reader does. A component whose value is not a single
/// int32 at this state -- because the state splits it into several paths, or
/// because a view it reads is gone -- is refused rather than guessed.
fn pure_ranking_measure_term(
    expression: &SpecExpression,
    state: &CState,
    reader: &mut CRankingMeasureReader<'_>,
) -> Result<Bitvector32Term, String> {
    let paths = crate::kernel::spec::evaluate_spec_expression_paths_with_loop_entry(
        state,
        expression,
        None,
        reader.assumptions,
        reader.budget,
    )
    .map_err(|error| format!("could not evaluate a termination measure: {error:?}"))?;
    let [path] = paths.as_slice() else {
        return Err(format!(
            "a termination measure must have exactly one value at this state; this one has {}",
            paths.len()
        ));
    };
    let (CValue::Int32(value) | CValue::UInt8(value)) = &path.value else {
        return Err("termination measures must be int32 expressions".into());
    };
    reader.reads.obligations.extend(path.obligations.clone());
    reader.reads.facts.extend(path.facts.clone());
    Ok(canonical_ranking_term(value))
}

/// The value of one memory read inside a measure, at `state`.
fn c_ranking_measure_read(
    expression: &CExpression,
    state: &CState,
    reader: &mut CRankingMeasureReader<'_>,
) -> Result<Bitvector32Term, String> {
    if matches!(expression, CExpression::TypedLoad { volatile: true, .. }) {
        return Err("a termination measure may not read a volatile object".into());
    }
    let paths = evaluate_c_expression_paths(state, expression, reader.assumptions, reader.budget)
        .map_err(|error| {
        format!("could not evaluate a termination measure's read: {error:?}")
    })?;
    let [path] = paths.as_slice() else {
        return Err(
            "a termination measure's read must have exactly one value at this state".into(),
        );
    };
    let (CExpressionOutcome::Value(CValue::Int32(value))
    | CExpressionOutcome::Value(CValue::UInt8(value))) = &path.outcome
    else {
        return Err("termination measures must be int32 expressions".into());
    };
    reader.reads.facts.extend(path.facts.iter().cloned());
    reader
        .reads
        .obligations
        .extend(path.obligations.iter().cloned());
    Ok(value.clone())
}

fn c_ranking_measure_term_unfolded(
    expression: &CExpression,
    state: &CState,
    reader: &mut CRankingMeasureReader<'_>,
) -> Result<Bitvector32Term, String> {
    use CExpression::*;
    fn binary(
        left: &CExpression,
        right: &CExpression,
        state: &CState,
        reader: &mut CRankingMeasureReader<'_>,
        operation: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
    ) -> Result<Bitvector32Term, String> {
        Ok(operation(
            c_ranking_measure_term_unfolded(left, state, reader)?,
            c_ranking_measure_term_unfolded(right, state, reader)?,
        ))
    }
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
        } => c_ranking_measure_term_unfolded(expression, state, reader),
        Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            let (condition, value) = c_ranking_measure_condition_term(condition, state, reader)?;
            let then_term = c_ranking_measure_term_unfolded(then_branch, state, reader)?;
            let else_term = c_ranking_measure_term_unfolded(else_branch, state, reader)?;
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
        Add(left, right) => binary(left, right, state, reader, Bitvector32Term::add),
        Subtract(left, right) => binary(left, right, state, reader, Bitvector32Term::subtract),
        Multiply(left, right) => binary(left, right, state, reader, Bitvector32Term::multiply),
        Divide(left, right) => binary(left, right, state, reader, Bitvector32Term::divide),
        Remainder(left, right) => binary(left, right, state, reader, Bitvector32Term::remainder),
        ShiftLeft(left, right) => binary(left, right, state, reader, Bitvector32Term::shift_left),
        ShiftRight(left, right) => binary(
            left,
            right,
            state,
            reader,
            Bitvector32Term::arithmetic_shift_right,
        ),
        BitwiseAnd(left, right) => binary(left, right, state, reader, Bitvector32Term::bitwise_and),
        BitwiseOr(left, right) => binary(left, right, state, reader, Bitvector32Term::bitwise_or),
        BitwiseXor(left, right) => binary(left, right, state, reader, Bitvector32Term::bitwise_xor),
        BitwiseNot(value) => Ok(Bitvector32Term::bitwise_not(
            c_ranking_measure_term_unfolded(value, state, reader)?,
        )),
        Cast { .. }
        | FloatNegate(_)
        | FloatClassification { .. }
        | FunctionAddress(_)
        | AddressOf(_)
        | PointerOffsetBytes { .. } => {
            Err("termination measures may only use scalar int32 expressions".into())
        }
        Load(_) | TypedLoad { .. } | Index(_, _) => {
            c_ranking_measure_read(expression, state, reader)
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
    reader: &mut CRankingMeasureReader<'_>,
) -> Result<(ConditionTerm, bool), String> {
    use CExpression::*;
    fn binary(
        left: &CExpression,
        right: &CExpression,
        state: &CState,
        reader: &mut CRankingMeasureReader<'_>,
        operation: fn(Bitvector32Term, Bitvector32Term) -> ConditionTerm,
    ) -> Result<(ConditionTerm, bool), String> {
        Ok((
            operation(
                c_ranking_measure_term_unfolded(left, state, reader)?,
                c_ranking_measure_term_unfolded(right, state, reader)?,
            ),
            true,
        ))
    }
    match expression {
        LessThan(left, right) => {
            binary(left, right, state, reader, ConditionTerm::signed_less_than)
        }
        LessEqual(left, right) => {
            binary(left, right, state, reader, ConditionTerm::signed_less_equal)
        }
        GreaterThan(left, right) => binary(
            left,
            right,
            state,
            reader,
            ConditionTerm::signed_greater_than,
        ),
        GreaterEqual(left, right) => binary(
            left,
            right,
            state,
            reader,
            ConditionTerm::signed_greater_equal,
        ),
        Equal(left, right) => binary(left, right, state, reader, ConditionTerm::equal),
        NotEqual(left, right) => {
            let (condition, _) = binary(left, right, state, reader, ConditionTerm::equal)?;
            Ok((condition, false))
        }
        Not(inner) => {
            let (condition, value) = c_ranking_measure_condition_term(inner, state, reader)?;
            Ok((condition, !value))
        }
        And(_, _) | Or(_, _) => {
            Err("compound boolean conditions are not atomic ranking measure conditions".into())
        }
        _ => Ok((
            ConditionTerm::equal(
                c_ranking_measure_term_unfolded(expression, state, reader)?,
                Bitvector32Term::Constant(0),
            ),
            false,
        )),
    }
}

/// The recursion anchor for one C function at its own entry state, or `None`
/// when the function declares no expression `decreases` measure.
///
/// This is the only construction of a [`CRecursionAnchor`]. The measure is
/// read off `function`'s contract interface, never from a caller argument, so
/// asking for an anchor cannot choose what the anchor ranks; the caller
/// chooses only which function and which entry. Reading it once here, at the
/// entry, is what makes M0 the value the whole recursion starts from: every
/// self-call inside this certification is compared to this one term.
///
/// A measure that reads memory owes the loadability of its reads. Those
/// obligations are kept on the anchor and emitted at the self-call, where the
/// path context can discharge them, rather than dropped.
///
/// Work is the declared measure, and the evaluation it needs; nothing
/// ambient is scanned.
pub(super) fn c_function_recursion_anchor(
    function: &CFunction,
    entry_state: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Result<Option<CRecursionAnchor>, String> {
    let Some(component) = function.contract_interface().recursion_measure() else {
        return Ok(None);
    };
    let mut reader = CRankingMeasureReader {
        assumptions,
        budget,
        reads: Default::default(),
    };
    let measure = c_ranking_measure_term(component, entry_state, &mut reader).map_err(|error| {
        format!(
            "the `decreases` measure `{}` of `{}` could not be read at its own entry state: \
             {error}",
            c_ranking_measure_display(component),
            function.name()
        )
    })?;
    let reads = reader.reads;
    let read_assumptions = assumptions_with_path_context(assumptions, &reads.facts, &[]);
    let mut entry_obligations = Vec::new();
    for obligation in &reads.obligations {
        add_required_proof_obligation_without_search(
            &mut entry_obligations,
            &read_assumptions,
            obligation.proposition().clone(),
            Some("a recursion measure's read is viewable at the function entry"),
            None,
        );
    }
    Ok(Some(CRecursionAnchor {
        function: function.name().to_string(),
        component: component.clone(),
        measure,
        entry_obligations,
    }))
}

/// The ranking members one self-call owes, against the anchor's M0.
///
/// The callee's declared measure is read at `state`, the same state the
/// callee's preconditions are read at, so the parameters it names hold the
/// arguments this call passes and a read it performs sees the memory the
/// callee will see. The two members are the function-level form of the loop's
/// back-edge bundle: the callee's measure is nonnegative, and it is strictly
/// below the value the caller's own entry gave. A recursion whose every step
/// satisfies both cannot be infinite, whatever the measure counts.
pub(super) fn collect_recursion_descent_obligations(
    anchor: &CRecursionAnchor,
    state: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Result<Vec<ProofObligation>, String> {
    let component = anchor.component();
    let mut reader = CRankingMeasureReader {
        assumptions,
        budget,
        reads: Default::default(),
    };
    let called = c_ranking_measure_term(component, state, &mut reader).map_err(|error| {
        format!(
            "the `decreases` measure `{}` of `{}` could not be read at the recursive call: \
             {error}",
            c_ranking_measure_display(component),
            anchor.function()
        )
    })?;
    let reads = reader.reads;
    let read_assumptions = assumptions_with_path_context(assumptions, &reads.facts, &[]);
    let context = format!("{} recursion measure", anchor.function());
    let mut obligations = Vec::new();
    for obligation in anchor
        .entry_obligations()
        .iter()
        .chain(reads.obligations.iter())
    {
        add_required_proof_obligation_without_search(
            &mut obligations,
            &read_assumptions,
            obligation.proposition().clone(),
            Some(&context),
            None,
        );
    }
    let display = c_ranking_measure_display(component);
    obligations.push(
        ProofObligation::verification_condition(ranking_nonnegative_proposition(&called))
            .with_introductions(LoweringIntroductions::new())
            .with_context(format!(
                "{context}: `{display}` is nonnegative at the recursive call"
            )),
    );
    obligations.push(
        ProofObligation::verification_condition(ranking_decrease_proposition(
            &called,
            anchor.measure(),
            component,
        )?)
        .with_introductions(LoweringIntroductions::new())
        .with_context(format!(
            "{context}: `{display}` decreases at the recursive call"
        )),
    );
    Ok(obligations)
}

/// The display form of one `decreases` component, for bundle member contexts.
pub(super) fn c_ranking_measure_display(measure: &CRankingComponent) -> String {
    match measure {
        CRankingComponent::CExpression(expression) => termination_measure_display(expression),
        // A pure component is shown as it was declared: its lowered form is a
        // specification tree with no source spelling of its own.
        CRankingComponent::Pure { source, .. } | CRankingComponent::PureInteger { source, .. } => {
            source.clone()
        }
    }
}

/// The display form of a whole `decreases` clause.
pub(super) fn c_ranking_measures_display(measures: &[CRankingComponent]) -> String {
    join_measure_components(measures.iter().map(c_ranking_measure_display))
}

/// The display form of one loop's declared measure, for plan diagnostics.
fn loop_termination_measure_display(measure: &CLoopTerminationMeasure) -> String {
    match measure {
        CLoopTerminationMeasure::Ranking(measures) => {
            join_measure_components(measures.iter().map(|measure| match measure {
                CRankingMeasureKey::CExpression(expression) => {
                    termination_measure_display(expression)
                }
                CRankingMeasureKey::Pure(source) => source.clone(),
            }))
        }
        CLoopTerminationMeasure::Structural(binder) => binder.clone(),
    }
}

fn join_measure_components(components: impl Iterator<Item = String>) -> String {
    let components = components.collect::<Vec<_>>();
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
    charge_termination_work(1);
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
        CStatement::TryCatchInt32 {
            try_body, handler, ..
        } => loop_at_index(try_body, target, next_index)
            .or_else(|| loop_at_index(handler, target, next_index)),
        CStatement::ForStep { step, .. } => loop_at_index(step, target, next_index),
        // Spelled out, as in `check_loops`: the two walks number the same
        // loops only while they descend into the same statements, so a new
        // statement kind must be placed in both.
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assign { .. }
        | CStatement::CallAssign { .. }
        | CStatement::Call { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Throw(_)
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::CopyAggregate { .. }
        | CStatement::Update { .. } => None,
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
            CStatement::ForStep {
                step: left_step,
                exited_locals: left_locals,
                continue_after: left_continue,
            },
            CStatement::ForStep {
                step: right_step,
                exited_locals: right_locals,
                continue_after: right_continue,
            },
        ) => {
            left_locals == right_locals
                && left_continue == right_continue
                && same_statement_shape(left_step, right_step)
        }
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
) -> Result<BTreeMap<usize, CLoopTerminationMeasure>, CTerminationError> {
    let mut certified: BTreeMap<usize, CLoopTerminationMeasure> = BTreeMap::new();
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
            ranking_measures,
            structural_measure,
            ..
        } = &rule.loop_statement
        else {
            return Err(error(format!(
                "verified loop rule for `{function_name}` is not a while loop"
            )));
        };
        for component in ranking_measures {
            reject_address_escaped_ranking_component(function_name, component, source_body)?;
        }
        let measure = match structural_measure {
            Some(binder) => CLoopTerminationMeasure::Structural(binder.clone()),
            None if ranking_measures.is_empty() => continue,
            None => CLoopTerminationMeasure::Ranking(
                ranking_measures
                    .iter()
                    .map(CRankingComponent::key)
                    .collect(),
            ),
        };
        if let Some(existing) = certified.get(&index) {
            if existing != &measure {
                return Err(error(format!(
                    "verified loop rules for `{function_name}` disagree on loop {index} `decreases`"
                )));
            }
        } else {
            certified.insert(index, measure);
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

/// Every loop of `statement`, in the order `check_loops` numbers them.
fn collect_loops<'a>(statement: &'a CStatement, loops: &mut Vec<&'a CStatement>) {
    charge_termination_work(1);
    match statement {
        CStatement::While { body, .. } => {
            loops.push(statement);
            collect_loops(body, loops);
        }
        CStatement::Seq(first, second) => {
            collect_loops(first, loops);
            collect_loops(second, loops);
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_loops(then_branch, loops);
            collect_loops(else_branch, loops);
        }
        CStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            collect_loops(try_body, loops);
            collect_loops(handler, loops);
        }
        CStatement::Switch { cases, .. } => {
            for case in cases {
                collect_loops(&case.body, loops);
            }
        }
        CStatement::ForStep { step, .. } => collect_loops(step, loops),
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assign { .. }
        | CStatement::CallAssign { .. }
        | CStatement::Call { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Throw(_)
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::CopyAggregate { .. }
        | CStatement::Update { .. } => {}
    }
}

/// The loops of a certified function that certification executed to their
/// exit, by source index.
///
/// Execution summarizes a loop only when the loop carries annotations: a
/// verified loop rule applies to a loop with invariant or effect checks, and
/// the invariant route runs for one with checks or a measure. A loop with none
/// of them has one route, the concrete one, which takes the loop one budgeted
/// iteration at a time and returns only when every feasible path has left it.
/// A function's verified rule exists because certification executed exactly
/// this body, so such a loop was run to its exit on every path the contract
/// admits and owes no measure.
///
/// A loop whose only annotation is the frame check a function's owned
/// memory gives every loop has two routes, and the rule says which ran:
/// certified under `ApplyVerifiedRules`, an annotated loop is replaced by a
/// verified loop rule or, with none, yields no paths, so a certified body
/// ran such a loop concretely wherever no rule names it; certified under
/// `Verify`, it may have been summarized, and nothing is granted. Nothing is
/// granted either unless the certified body's loops are the source body's
/// loops, shape for shape, since the indices name source loops.
fn loops_executed_to_exit(
    function: &CFunction,
    loop_semantics: CLoopSemantics,
    ruled_loops: &BTreeSet<usize>,
) -> BTreeSet<usize> {
    let mut source_loops = Vec::new();
    collect_loops(&function.source_body, &mut source_loops);
    let mut certified_loops = Vec::new();
    collect_loops(function.body(), &mut certified_loops);
    if source_loops.len() != certified_loops.len()
        || source_loops
            .iter()
            .zip(&certified_loops)
            .any(|(source, certified)| !same_statement_shape(source, certified))
    {
        return BTreeSet::new();
    }
    certified_loops
        .iter()
        .enumerate()
        .filter(|(index, certified)| {
            let CStatement::While {
                invariant,
                invariant_checks,
                effect_checks,
                resource_specs,
                ranking_measures,
                structural_measure,
                ..
            } = certified
            else {
                return false;
            };
            let unsummarized = invariant.is_empty()
                && invariant_checks.is_empty()
                && resource_specs.is_empty()
                && ranking_measures.is_empty()
                && structural_measure.is_none();
            if !unsummarized {
                return false;
            }
            if effect_checks.is_empty() {
                return true;
            }
            effect_checks
                .iter()
                .all(|check| check.origin() == CLoopEffectOrigin::InheritedResourceDerived)
                && loop_semantics == CLoopSemantics::ApplyVerifiedRules
                && !ruled_loops.contains(index)
        })
        .map(|(index, _)| index)
        .collect()
}

/// Confirms that every loop the plan ranks has a checked back-edge bundle
/// for exactly that measure, and collects the index of every loop that
/// carries no measure at all. Every loop is visited, so the collected indices
/// and `next_index` describe the whole statement whichever loops are ranked.
///
/// This pass proves nothing. A loop's nonnegativity and lexicographic
/// decrease obligations are members of its `close_invariants` bundle, which
/// the loop's own verified rule already certified; the rule carries the
/// declared measure on its loop head, so matching it against the plan is the
/// whole of the check here.
fn check_loops(
    statement: &CStatement,
    supplied: &BTreeMap<usize, CLoopTerminationMeasure>,
    certified: &BTreeMap<usize, CLoopTerminationMeasure>,
    function_name: &str,
    next_index: &mut usize,
    unranked: &mut Vec<usize>,
) -> Result<(), CTerminationError> {
    charge_termination_work(1);
    match statement {
        CStatement::Seq(first, second) => {
            check_loops(
                first,
                supplied,
                certified,
                function_name,
                next_index,
                unranked,
            )?;
            check_loops(
                second,
                supplied,
                certified,
                function_name,
                next_index,
                unranked,
            )
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            check_loops(
                then_branch,
                supplied,
                certified,
                function_name,
                next_index,
                unranked,
            )?;
            check_loops(
                else_branch,
                supplied,
                certified,
                function_name,
                next_index,
                unranked,
            )
        }
        CStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            check_loops(
                try_body,
                supplied,
                certified,
                function_name,
                next_index,
                unranked,
            )?;
            check_loops(
                handler,
                supplied,
                certified,
                function_name,
                next_index,
                unranked,
            )
        }
        CStatement::While { body, .. } => {
            let index = *next_index;
            *next_index += 1;
            check_loops(
                body,
                supplied,
                certified,
                function_name,
                next_index,
                unranked,
            )?;
            let Some(measures) = supplied.get(&index) else {
                unranked.push(index);
                return Ok(());
            };
            if matches!(measures, CLoopTerminationMeasure::Ranking(components) if components.is_empty())
            {
                return Err(error(format!(
                    "loop {index} has an empty termination measure"
                )));
            }
            match certified.get(&index) {
                Some(checked) if checked == measures => Ok(()),
                Some(checked) => Err(error(format!(
                    "loop {index} in `{function_name}` was certified for `{}`, not the planned `{}`",
                    loop_termination_measure_display(checked),
                    loop_termination_measure_display(measures)
                ))),
                None => Err(error(format!(
                    "loop {index} in `{function_name}` has no verified loop rule carrying its \
                     `decreases` measure, so its back-edge ranking obligations were never checked"
                ))),
            }
        }
        CStatement::Switch { cases, .. } => {
            for case in cases {
                check_loops(
                    &case.body,
                    supplied,
                    certified,
                    function_name,
                    next_index,
                    unranked,
                )?;
            }
            Ok(())
        }
        CStatement::ForStep { step, .. } => check_loops(
            step,
            supplied,
            certified,
            function_name,
            next_index,
            unranked,
        ),
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assign { .. }
        | CStatement::CallAssign { .. }
        | CStatement::Call { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Throw(_)
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::CopyAggregate { .. }
        | CStatement::Update { .. } => Ok(()),
    }
}

/// The callees of one body, with a callee spelled like an object the function
/// binds recorded under a name no function can have.
///
/// C11 6.2.1p4 hides a file-scope function of the same name behind a
/// parameter or local, so such a call goes through that object. Resolving it
/// to the function would hand the call that function's ranking proof, so it is
/// left unranked, which is the treatment every indirect call gets.
fn termination_callees(function: &CFunction) -> BTreeSet<String> {
    let mut found = BTreeSet::new();
    statement_calls(&function.source_body, &mut found);
    let objects = function_object_names(function);
    found
        .into_iter()
        .map(|callee| {
            if objects.contains(&callee) {
                format!("{callee}#indirect")
            } else {
                callee
            }
        })
        .collect()
}

/// The named contracts this function's own `requires` clauses bind to a
/// function-pointer object, keeping only those declared `diverges`, keyed by
/// the object each clause names.
///
/// A contract is the whole of what a call through a pointer may assume: the
/// implementation behind the pointer is not known here, and one that never
/// returns satisfies a contract that admits divergence. So a requirement of
/// such a contract is this function's own admission that a pointer call of
/// its may not return, read from its own clauses with work linear in them.
fn diverging_contract_objects(
    function: &CFunction,
    diverging_contracts: &BTreeSet<String>,
) -> BTreeMap<String, String> {
    fn collect(
        requirement: &SpecProposition,
        diverging_contracts: &BTreeSet<String>,
        found: &mut BTreeMap<String, String>,
    ) {
        charge_termination_work(1);
        match requirement {
            SpecProposition::And(left, right) => {
                collect(left, diverging_contracts, found);
                collect(right, diverging_contracts, found);
            }
            SpecProposition::Predicate { name, arguments } => {
                let Some(contract) = CFunctionContract::surface_name_from_predicate(name) else {
                    return;
                };
                if !diverging_contracts.contains(contract) {
                    return;
                }
                let [
                    SpecPredicateArgument::Value(SpecExpression::CExpression(
                        CExpression::Variable(object),
                    )),
                ] = arguments.as_slice()
                else {
                    return;
                };
                found.insert(object.clone(), contract.to_string());
            }
            _ => {}
        }
    }

    let mut found = BTreeMap::new();
    if diverging_contracts.is_empty() {
        return found;
    }
    for requirement in function.contract_requires() {
        collect(requirement, diverging_contracts, &mut found);
    }
    found
}

/// The function a pointer value names, if it names one.
fn value_function_address(value: &CValue) -> Option<&str> {
    let CValue::Pointer(pointer) = value else {
        return None;
    };
    match &pointer.pointer().block {
        PointerBlock::Function(name) => Some(name),
        _ => None,
    }
}

fn expression_function_addresses(expression: &CExpression, taken: &mut BTreeSet<String>) {
    use CExpression::*;
    match expression {
        FunctionAddress(name) => {
            taken.insert(name.clone());
        }
        Value(value) => {
            if let Some(name) = value_function_address(value) {
                taken.insert(name.to_string());
            }
        }
        Variable(_) => {}
        Cast { expression, .. }
        | FloatNegate(expression)
        | FloatClassification { expression, .. }
        | AddressOf(expression)
        | PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | TypedLoad {
            pointer: expression,
            ..
        }
        | Not(expression)
        | BitwiseNot(expression)
        | Load(expression) => expression_function_addresses(expression, taken),
        Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            expression_function_addresses(condition, taken);
            expression_function_addresses(then_branch, taken);
            expression_function_addresses(else_branch, taken);
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
            expression_function_addresses(left, taken);
            expression_function_addresses(right, taken);
        }
    }
}

fn statement_function_addresses(statement: &CStatement, taken: &mut BTreeSet<String>) {
    charge_termination_work(1);
    let mut visit = |expression: &CExpression| expression_function_addresses(expression, taken);
    match statement {
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. } => {}
        CStatement::Assign { expression, .. }
        | CStatement::Return(expression)
        | CStatement::Throw(expression) => visit(expression),
        CStatement::CallAssign { arguments, .. } | CStatement::Call { arguments, .. } => {
            arguments.iter().for_each(visit);
        }
        CStatement::HeapAllocate { bytes, .. } => visit(bytes),
        CStatement::HeapFree { pointer } => visit(pointer),
        CStatement::Assert { condition, .. } => visit(condition),
        CStatement::Store { pointer, value } | CStatement::TypedStore { pointer, value, .. } => {
            visit(pointer);
            visit(value);
        }
        CStatement::CopyAggregate { target, source, .. } => {
            visit(target);
            visit(source);
        }
        CStatement::Update {
            target, operand, ..
        } => {
            visit(target);
            visit(operand);
        }
        CStatement::ForStep { step, .. } => statement_function_addresses(step, taken),
        CStatement::Seq(first, second) => {
            statement_function_addresses(first, taken);
            statement_function_addresses(second, taken);
        }
        CStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            statement_function_addresses(try_body, taken);
            statement_function_addresses(handler, taken);
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            visit(condition);
            statement_function_addresses(then_branch, taken);
            statement_function_addresses(else_branch, taken);
        }
        CStatement::While {
            condition, body, ..
        } => {
            visit(condition);
            statement_function_addresses(body, taken);
        }
        CStatement::Switch { expression, cases } => {
            visit(expression);
            for case in cases {
                statement_function_addresses(&case.body, taken);
            }
        }
    }
}

/// Every function whose address `function` takes: in its body, and in the
/// initial values of the static storage it links, which is where a `const`
/// callback table names its entries. These are all the ways a function in
/// the verified set becomes the target of a function pointer.
fn function_address_taken(function: &CFunction, taken: &mut BTreeSet<String>) {
    statement_function_addresses(&function.source_body, taken);
    let scalars = function
        .global_variables()
        .iter()
        .map(|global| &global.initial_value)
        .chain(
            function
                .static_variables()
                .iter()
                .map(|local| &local.initial_value),
        );
    let arrays = function
        .global_arrays()
        .iter()
        .flat_map(|array| &array.initial_values)
        .chain(
            function
                .static_arrays()
                .iter()
                .flat_map(|array| &array.initial_values),
        );
    let aggregates = function
        .global_aggregates()
        .iter()
        .flat_map(|aggregate| &aggregate.initializers)
        .chain(
            function
                .global_aggregate_arrays()
                .iter()
                .flat_map(|aggregate| &aggregate.initializers),
        )
        .chain(
            function
                .static_aggregates()
                .iter()
                .flat_map(|aggregate| &aggregate.initializers),
        )
        .chain(
            function
                .static_aggregate_arrays()
                .iter()
                .flat_map(|aggregate| &aggregate.initializers),
        )
        .map(|initializer| &initializer.value);
    for value in scalars.chain(arrays).chain(aggregates) {
        charge_termination_work(1);
        if let Some(name) = value_function_address(value) {
            taken.insert(name.to_string());
        }
    }
}

/// The verified functions of one run, the contract-less `static inline`
/// helpers their bodies reach, and each node's callees.
///
/// A call to such a helper executes that body at the call site, so the helper
/// is a node of this call graph exactly like the function whose body contains
/// the call. A helper that carries its own sidecar contract already has a
/// verified rule and stays that node; only the contract-less ones are added,
/// only the ones the verified bodies actually reach, and each is read once.
type TerminationCallGraph<'a> = (
    BTreeMap<String, &'a CFunction>,
    BTreeMap<String, BTreeSet<String>>,
);

fn termination_call_graph<'a>(
    partial_rules: &'a [CVerifiedFunctionRule],
    inline_bodies: &[&'a CFunction],
) -> TerminationCallGraph<'a> {
    let mut functions = partial_rules
        .iter()
        .map(|rule| (rule.function.name.clone(), &rule.function))
        .collect::<BTreeMap<_, _>>();
    charge_termination_work(partial_rules.len() + inline_bodies.len());
    let unruled_bodies = inline_bodies
        .iter()
        .filter(|function| !functions.contains_key(function.name()))
        .map(|function| (function.name().to_string(), *function))
        .collect::<BTreeMap<_, _>>();
    let mut calls = BTreeMap::<String, BTreeSet<String>>::new();
    let mut pending = functions.keys().cloned().collect::<Vec<_>>();
    while let Some(name) = pending.pop() {
        charge_termination_work(1);
        if calls.contains_key(&name) {
            continue;
        }
        let function = *functions
            .get(&name)
            .expect("every pending name was added with its function");
        let found = termination_callees(function);
        for callee in &found {
            charge_termination_work(1);
            if functions.contains_key(callee) {
                continue;
            }
            let Some(helper) = unruled_bodies
                .get(callee)
                .filter(|helper| helper.has_inline_body())
            else {
                continue;
            };
            functions.insert(callee.clone(), *helper);
            pending.push(callee.clone());
        }
        // A contract-less function whose address is taken has no rule to
        // answer for it either: a function pointer resolved to it executes
        // its body in place, so that body is a node too.
        let mut taken = BTreeSet::new();
        function_address_taken(function, &mut taken);
        for callback in taken {
            charge_termination_work(1);
            if functions.contains_key(&callback) {
                continue;
            }
            if let Some(body) = unruled_bodies.get(&callback) {
                functions.insert(callback.clone(), *body);
                pending.push(callback);
            }
        }
        calls.insert(name, found);
    }
    (functions, calls)
}

/// What an expression `decreases` measure asks of the function that declares
/// it (D6, slice 1: direct self-recursion).
///
/// The other two function-level measures are analyses of the body: the
/// checker walks the recursion paths itself and decides that the named
/// parameter or resource descends. This one is not. The descent is an
/// ordinary proof obligation, emitted by the kernel at every application of
/// this function's contract while this function is being certified, and
/// discharged in the proof like any other. So the only thing left for this
/// judgment is to check that those obligations were reachable and complete:
///
/// * the certified function's own contract interface carries the measure.
///   The plan is untrusted and names only a spelling; the interface is what
///   [`crate::kernel::c_execution_environment_with_recursion_anchor`] reads
///   to build the anchor, and the certified [`CFunction`] here is the one the
///   rule was issued for, so a measure present here is a measure that was
///   anchored. A plan claiming a measure the interface does not carry is a
///   plan for obligations nobody emitted, and it is refused.
/// * every recursive edge of this component is a call to this function
///   itself. The anchor names one function, so a call to a *different*
///   member of the cycle owes nothing, and a two-function cycle would be
///   certified with no descent anywhere. Such a component is refused by name
///   rather than admitted; `decreases <parameter>` still ranks it.
/// * the function does not have an inline body. An inline body executes at
///   the call site instead of applying a contract, so no call step reads the
///   anchor and no obligation is emitted at all.
/// * every loop the self-call sits inside was certified under this function's
///   anchor. A loop is verified once as its own judgment and then applied as
///   a summary, so a call the summary swallowed owes nothing at the step that
///   applies it; what makes it owe the descent is that the loop's own body
///   was stepped under the anchor. The certified [`CVerifiedLoopRule`] records
///   which anchor that was — the kernel writes it from the environment the
///   paths were produced in, and the surface has no way to set it — so this
///   reads the rule, never the plan, which names only a spelling.
///
/// Work is the component's own members and this function's own statement
/// tree; nothing ambient is scanned.
fn check_expression_measure_recursion(
    name: &str,
    source: &str,
    function: &CFunction,
    recursive_callees: &BTreeSet<String>,
    plans: &BTreeMap<String, &CFunctionTerminationPlan>,
    loop_rules: &[CVerifiedLoopRule],
) -> Result<(), CTerminationError> {
    if function.contract_interface().recursion_measure().is_none() {
        return Err(error(format!(
            "the termination plan ranks `{name}` by the expression measure `{source}`, but the \
             certified `{name}` carries no declared measure, so no recursive call of it owed a \
             descent obligation"
        )));
    }
    if function.has_inline_body() {
        return Err(error(format!(
            "`{name}` declares the expression `decreases` measure `{source}` and has an inline \
             body. An inline body executes at each call site instead of applying `{name}`'s \
             contract, so a self-call inside it is never ranked. Give `{name}` a Click contract, \
             or rank it with `decreases <int32 parameter>`"
        )));
    }
    for callee in recursive_callees {
        charge_termination_work(1);
        if callee == name {
            continue;
        }
        return Err(error(format!(
            "`{name}` declares the expression `decreases` measure `{source}` and is in a \
             recursive component with `{callee}`. An expression measure currently ranks direct \
             self-recursion only: the descent is owed at a call to the function that declared \
             the measure, so a call to `{callee}` would be ranked by nothing. Rank this component \
             with `decreases <int32 parameter>`"
        )));
    }
    // Every member of a settled component agrees on its measure kind. With
    // the loop above, the component is `{name}` alone, so this reads one plan.
    if !matches!(
        plans
            .get(name)
            .and_then(|plan| plan.recursive_measure.as_ref()),
        Some(CFunctionTerminationMeasure::Expression(_))
    ) {
        return Err(error(
            "a recursive component cannot mix an expression measure with another measure kind",
        ));
    }
    // A loop is verified once, as its own judgment, and then applied as a
    // summary, so a self-call the summary swallowed owes nothing at the step
    // that applies it. What makes it owe the descent is the loop's own body
    // having been stepped under this function's anchor, and a rule records
    // the anchor it was produced under. Every loop the call sits inside is
    // required to carry it, innermost and enclosing alike: an enclosing loop
    // certified without the anchor is a summary that swallowed the inner
    // one's, so the requirement is the same at every level and nesting needs
    // no separate case.
    let declared = function.contract_interface().recursion_measure();
    let mut next_index = 0;
    let mut enclosing = Vec::new();
    let mut self_call_loops = BTreeSet::new();
    self_call_loop_indices(
        &function.source_body,
        name,
        &mut next_index,
        &mut enclosing,
        &mut self_call_loops,
    );
    for index in self_call_loops {
        charge_termination_work(1);
        // The rule is bound to this source loop the way
        // `verified_loop_ranking_measures` binds one: by index and executable
        // shape. Reading the shape here too keeps this check standing on its
        // own rather than on that later pass's ordering. The source loop is
        // looked up once per index, not once per rule.
        let source_loop = loop_at_index(&function.source_body, index, &mut 0);
        let anchored = loop_rules.iter().any(|rule| {
            rule.loop_index == Some(index)
                && rule
                    .recursion_anchor
                    .as_ref()
                    .is_some_and(|anchor| anchor.ranks(name, declared))
                && source_loop.is_some_and(|source_loop| {
                    same_statement_shape(source_loop, &rule.loop_statement)
                })
        });
        if !anchored {
            return Err(error(format!(
                "`{name}` declares the expression `decreases` measure `{source}` and calls itself \
                 inside loop {index}, whose verified rule was certified without `{name}`'s \
                 recursion anchor. A loop is verified as its own judgment and then applied as a \
                 summary, so the descent at that call would be owed by no step of `{name}`'s \
                 proof. Give loop {index} a `decreases` clause and a proof of its own, rank \
                 `{name}` with `decreases <int32 parameter>`, or lift the recursive call out of \
                 the loop"
            )));
        }
    }
    Ok(())
}

/// Whether `statement` contains a call to `callee`, at any depth.
///
/// Work is the statement tree handed in; nothing outside it is read.
pub(super) fn statement_calls_function(statement: &CStatement, callee: &str) -> bool {
    charge_termination_work(1);
    let both = |left: &CStatement, right: &CStatement| {
        statement_calls_function(left, callee) || statement_calls_function(right, callee)
    };
    match statement {
        CStatement::Call { function_name, .. } | CStatement::CallAssign { function_name, .. } => {
            function_name == callee
        }
        CStatement::While { body, .. } => statement_calls_function(body, callee),
        CStatement::Seq(left, right) => both(left, right),
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => both(then_branch, else_branch),
        CStatement::TryCatchInt32 {
            try_body, handler, ..
        } => both(try_body, handler),
        CStatement::Switch { cases, .. } => cases
            .iter()
            .any(|case| statement_calls_function(&case.body, callee)),
        CStatement::ForStep { step, .. } => statement_calls_function(step, callee),
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assign { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Throw(_)
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::CopyAggregate { .. }
        | CStatement::Update { .. } => false,
    }
}

/// The source loop indices of every loop in `body` that contains a call to
/// `callee`, an enclosing loop as well as the innermost one.
///
/// The numbering is the one [`loop_at_index`] and [`check_loops`] use, so an
/// index here names the same loop a certified rule's `loop_index` does. A
/// loop inside an `if`, a `switch`, or another loop is numbered like any
/// other, which is what keeps those shapes checked rather than skipped.
///
/// Work is the statement tree, which is this function's own body; nothing
/// outside it is read.
fn self_call_loop_indices(
    statement: &CStatement,
    callee: &str,
    next_index: &mut usize,
    enclosing: &mut Vec<usize>,
    found: &mut BTreeSet<usize>,
) {
    charge_termination_work(1);
    let mut descend = |statement: &CStatement, next_index: &mut usize| {
        self_call_loop_indices(statement, callee, next_index, enclosing, found);
    };
    match statement {
        CStatement::Call { function_name, .. } | CStatement::CallAssign { function_name, .. } => {
            if function_name == callee {
                found.extend(enclosing.iter().copied());
            }
        }
        CStatement::While { body, .. } => {
            let index = *next_index;
            *next_index += 1;
            enclosing.push(index);
            self_call_loop_indices(body, callee, next_index, enclosing, found);
            enclosing.pop();
        }
        CStatement::Seq(first, second) => {
            descend(first, next_index);
            descend(second, next_index);
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            descend(then_branch, next_index);
            descend(else_branch, next_index);
        }
        CStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            descend(try_body, next_index);
            descend(handler, next_index);
        }
        CStatement::Switch { cases, .. } => {
            for case in cases {
                descend(&case.body, next_index);
            }
        }
        CStatement::ForStep { step, .. } => descend(step, next_index),
        // Spelled out, as in `loop_at_index` and `check_loops`: these walks
        // number the same loops only while they descend into the same
        // statements, so a new statement kind must be placed in all of them.
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assign { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Throw(_)
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::CopyAggregate { .. }
        | CStatement::Update { .. } => {}
    }
}

/// Proposes a height for every node of the termination call graph: zero for a
/// function that calls no other node, and otherwise one more than its highest
/// callee outside its own recursive cycle. The members of a cycle share a
/// height.
///
/// The result is untrusted. [`c_verified_function_termination_rules`] checks
/// at every call site that the callee is not above its caller, and treats
/// every call between equal heights as a recursive edge that a declared
/// measure must rank, so a wrong height can only refuse a function or fail
/// the check; it cannot certify one. This is Tarjan's algorithm with an
/// explicit stack, so a call chain as deep as the project is long costs heap
/// and not machine stack. Work is linear in the nodes and their call edges.
pub fn c_termination_height_plan(
    partial_rules: &[CVerifiedFunctionRule],
    inline_bodies: &[&CFunction],
) -> BTreeMap<String, usize> {
    let (functions, calls) = termination_call_graph(partial_rules, inline_bodies);
    let names = functions.keys().collect::<Vec<_>>();
    let node_of = names
        .iter()
        .enumerate()
        .map(|(node, name)| (name.as_str(), node))
        .collect::<BTreeMap<_, _>>();
    let edges = names
        .iter()
        .map(|name| {
            charge_termination_work(1);
            calls[*name]
                .iter()
                .inspect(|_| charge_termination_work(1))
                .filter_map(|callee| node_of.get(callee.as_str()).copied())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    const UNVISITED: usize = usize::MAX;
    let mut discovery = vec![UNVISITED; names.len()];
    let mut low = vec![0; names.len()];
    let mut on_stack = vec![false; names.len()];
    let mut height = vec![UNVISITED; names.len()];
    let mut stack = Vec::new();
    let mut next_discovery = 0;
    for root in 0..names.len() {
        if discovery[root] != UNVISITED {
            continue;
        }
        // Each frame is a node and the position of its next unexplored edge.
        let mut frames = vec![(root, 0)];
        while let Some((node, edge)) = frames.last().copied() {
            charge_termination_work(1);
            if edge == 0 {
                discovery[node] = next_discovery;
                low[node] = next_discovery;
                next_discovery += 1;
                stack.push(node);
                on_stack[node] = true;
            }
            if let Some(callee) = edges[node].get(edge).copied() {
                frames.last_mut().expect("the frame was just read").1 += 1;
                if discovery[callee] == UNVISITED {
                    frames.push((callee, 0));
                } else if on_stack[callee] {
                    low[node] = low[node].min(discovery[callee]);
                }
                continue;
            }
            frames.pop();
            if let Some((caller, _)) = frames.last() {
                low[*caller] = low[*caller].min(low[node]);
            }
            if low[node] != discovery[node] {
                continue;
            }
            // `node` roots a finished cycle. Every callee outside it was
            // finished earlier, so its height is already known.
            let first_member = stack
                .iter()
                .rposition(|member| *member == node)
                .expect("a cycle root is on the stack");
            let members = stack.split_off(first_member);
            charge_termination_work(members.len());
            for member in &members {
                on_stack[*member] = false;
            }
            let cycle_height = members
                .iter()
                .flat_map(|member| edges[*member].iter())
                .inspect(|_| charge_termination_work(1))
                .filter(|callee| height[**callee] != UNVISITED)
                .map(|callee| height[*callee] + 1)
                .max()
                .unwrap_or(0);
            for member in members {
                height[member] = cycle_height;
            }
        }
    }
    names
        .into_iter()
        .zip(height)
        .map(|(name, height)| (name.clone(), height))
        .collect()
}

/// Why a function has no termination evidence. Exactly one reason is
/// reported per function: its own first unranked loop if it has one, and
/// otherwise the first call that is not shown to descend.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CTerminationRefusal {
    /// The loop at this index, in source order, declares no measure.
    UnrankedLoop { index: usize },
    /// A call to `callee` closes a recursive cycle, and the caller or
    /// `callee` declares no function-level measure to rank it.
    UnmeasuredRecursion { callee: String },
    /// `callee` has no termination evidence of its own.
    Callee { callee: String },
    /// A call through the object `object` is authorized by the named contract
    /// `contract`, which is declared `diverges`. A contract is the whole of
    /// what a pointer call may assume, so one that admits divergence admits an
    /// execution of this call that never returns.
    DivergingContract { object: String, contract: String },
    /// A call through the object `object` has no declared callee.
    IndirectCall { object: String },
    /// The function declares that it may not return, and nothing else about
    /// it withholds evidence.
    DeclaredDiverging,
}

impl std::fmt::Display for CTerminationRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnrankedLoop { index } => {
                write!(formatter, "loop {index} declares no `decreases` measure")
            }
            Self::UnmeasuredRecursion { callee } => write!(
                formatter,
                "the recursive call to `{callee}` is ranked by no function-level `decreases` measure"
            ),
            Self::Callee { callee } => {
                write!(formatter, "callee `{callee}` has no termination evidence")
            }
            Self::DivergingContract { object, contract } => write!(
                formatter,
                "the named contract `{contract}` is declared `diverges`, so the call through `{object}` may not return"
            ),
            Self::IndirectCall { object } => write!(
                formatter,
                "the call through `{object}` has no declared callee to descend to"
            ),
            Self::DeclaredDiverging => write!(formatter, "it is declared `diverges`"),
        }
    }
}

/// A function whose address `taker` takes, so that it may be called through a
/// function pointer, although it is not shown to return without going through
/// a function pointer itself.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CUnsuitableCallback {
    pub taker: String,
    pub callback: String,
}

/// The outcome of one termination check: evidence for the functions shown to
/// return, and one reason for each function that was not.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CTerminationVerdicts {
    pub rules: Vec<CVerifiedFunctionTerminationRule>,
    pub refusals: BTreeMap<String, CTerminationRefusal>,
    /// Functions declared diverging that this check would otherwise have
    /// certified: every loop ranked and every call descending. They receive
    /// no evidence, and the caller of this check decides what an unjustified
    /// declaration means.
    pub unjustified_diverging: Vec<String>,
    /// Address-takings that keep every call through a function pointer
    /// refused. While this is nonempty the verdicts are the strict ones, and
    /// `refusals` says why each named callback does not qualify.
    pub unsuitable_callbacks: Vec<CUnsuitableCallback>,
}

/// Checks untrusted ranking plans against exact partially-correct function
/// rules and returns the independently usable subset proved to terminate.
///
/// The judgment is local descent. `heights` is an untrusted proposal, as
/// [`c_termination_height_plan`] makes one: every call must reach a callee
/// that is not above its caller, a strictly lower callee must already have
/// evidence, and a callee at the caller's own height is a recursive edge that
/// the caller's declared measure must rank. Soundness is one induction on the
/// pair of height and measure, so nothing here searches the call graph: each
/// function reads its own call sites and loops, and levels are settled in
/// ascending order with work linear in their recursive edges.
///
/// `assumed_terminating` names callees outside the verified set whose
/// declarations promise that they return: an external contract, or a function
/// this run did not select. They are assumptions in the same sense as those
/// callees' postconditions.
///
/// `declared_diverging` names verified functions whose declarations say they
/// may not return. Such a function is checked like any other, so the verdict
/// can say whether the declaration was needed, but it never receives
/// evidence and its callers are refused for it.
///
/// `diverging_contracts` names the named function-pointer contracts whose
/// declarations say the same. A contract is the whole of what a call through
/// a pointer may assume, so a function that requires one of these admits an
/// execution of its pointer calls that never returns, and receives no
/// evidence whatever its callees do.
pub fn c_verified_function_termination_rules(
    partial_rules: &[CVerifiedFunctionRule],
    plan_entries: &[CFunctionTerminationPlan],
    verified_loop_rules: &BTreeMap<String, Vec<CVerifiedLoopRule>>,
    inline_bodies: &[&CFunction],
    heights: &BTreeMap<String, usize>,
    assumed_terminating: &BTreeSet<String>,
    declared_diverging: &BTreeSet<String>,
    diverging_contracts: &BTreeSet<String>,
) -> Result<CTerminationVerdicts, CTerminationError> {
    let (functions, calls) = termination_call_graph(partial_rules, inline_bodies);
    let ruled = partial_rules
        .iter()
        .map(|rule| (rule.function.name(), rule))
        .collect::<BTreeMap<_, _>>();
    charge_termination_work(plan_entries.len());
    let plans = plan_entries
        .iter()
        .map(|plan| (plan.function_name.clone(), plan))
        .collect::<BTreeMap<_, _>>();
    if plans.len() != plan_entries.len() {
        return Err(error("termination plans contain a duplicate function"));
    }

    let height_of = |name: &str| {
        heights.get(name).copied().ok_or_else(|| {
            error(format!(
                "the termination height plan assigns no height to `{name}`"
            ))
        })
    };

    // Ascending height visits every strictly lower callee before its caller,
    // so a caller reads a verdict and never computes one. Functions of equal
    // height are one level, settled together below.
    let mut levels = BTreeMap::<usize, Vec<&String>>::new();
    for name in functions.keys() {
        charge_termination_work(1);
        levels.entry(height_of(name)?).or_default().push(name);
    }

    type Settled = (
        BTreeSet<String>,
        BTreeMap<String, CTerminationRefusal>,
        Vec<String>,
    );
    let settle = |allow_pointer_calls: bool| -> Result<Settled, CTerminationError> {
        let mut terminating = BTreeSet::<String>::new();
        let mut refusals = BTreeMap::<String, CTerminationRefusal>::new();
        let mut unjustified_diverging = Vec::new();
        for (height, level) in &levels {
            // The calls a function makes at its own height are its recursive
            // edges: the height does not rank them, so its declared measure must.
            let mut level_callers = BTreeMap::<&str, Vec<&String>>::new();
            let mut settled = Vec::<&String>::new();
            for name in level {
                charge_termination_work(1);
                let name = *name;
                let function = functions[name];
                let mut refusal = None;
                let mut recursive_callees = BTreeSet::<String>::new();
                let diverging_objects = diverging_contract_objects(function, diverging_contracts);
                for callee in &calls[name] {
                    charge_termination_work(1);
                    // `realloc` is a call in the syntax and a primitive in the
                    // semantics: execution models it before it looks for any
                    // function of that name, as it models the allocation and
                    // free statements, so it returns like they do.
                    if callee == MODELED_REALLOC {
                        continue;
                    }
                    if let Some(object) = callee.strip_suffix("#indirect") {
                        // A requirement names the object it constrains, and a
                        // pointer held in another of this function's objects
                        // may carry the same value, so one diverging contract
                        // withholds evidence from every pointer call here.
                        // The refusal names the contract the requirement puts
                        // on the object called, when there is one.
                        let diverging = diverging_objects
                            .get(object)
                            .or_else(|| diverging_objects.values().next());
                        if let Some(contract) = diverging {
                            if refusal.is_none()
                                || matches!(refusal, Some(CTerminationRefusal::IndirectCall { .. }))
                            {
                                refusal = Some(CTerminationRefusal::DivergingContract {
                                    object: object.to_string(),
                                    contract: contract.clone(),
                                });
                            }
                        } else if !allow_pointer_calls && refusal.is_none() {
                            refusal = Some(CTerminationRefusal::IndirectCall {
                                object: object.to_string(),
                            });
                        }
                        continue;
                    }
                    if !functions.contains_key(callee) {
                        if !assumed_terminating.contains(callee) && refusal.is_none() {
                            refusal = Some(CTerminationRefusal::Callee {
                                callee: callee.clone(),
                            });
                        }
                        continue;
                    }
                    let callee_height = height_of(callee)?;
                    if callee_height > *height {
                        return Err(error(format!(
                            "the termination height plan places callee `{callee}` at height {callee_height}, above its caller `{name}` at height {height}"
                        )));
                    }
                    if callee_height == *height {
                        recursive_callees.insert(callee.clone());
                        level_callers.entry(callee.as_str()).or_default().push(name);
                    } else if !terminating.contains(callee) && refusal.is_none() {
                        refusal = Some(CTerminationRefusal::Callee {
                            callee: callee.clone(),
                        });
                    }
                }

                let plan = plans.get(name);
                let recursive_measure = plan.and_then(|plan| plan.recursive_measure.clone());
                let mut parameter_indices = BTreeMap::new();
                let mut structural_requirement = None;
                if recursive_callees.is_empty() {
                    if recursive_measure.is_some() {
                        return Err(error(format!(
                            "function-level `decreases` on nonrecursive function `{name}` has no recursive edge to rank"
                        )));
                    }
                } else if let Some(unmeasured) = std::iter::once(name)
                    .chain(recursive_callees.iter())
                    .inspect(|_| charge_termination_work(1))
                    .find(|member| {
                        plans
                            .get(*member)
                            .and_then(|plan| plan.recursive_measure.as_ref())
                            .is_none()
                    })
                {
                    if refusal.is_none() {
                        refusal = Some(CTerminationRefusal::UnmeasuredRecursion {
                            callee: if unmeasured == name {
                                recursive_callees
                                    .first()
                                    .expect("a recursive function has a recursive callee")
                                    .clone()
                            } else {
                                unmeasured.clone()
                            },
                        });
                    }
                } else if let Some(CFunctionTerminationMeasure::ResourceRequirement(index)) =
                    recursive_measure
                {
                    if recursive_callees.len() != 1 || !recursive_callees.contains(name) {
                        return Err(error(
                            "structural resource termination currently supports direct recursion only",
                        ));
                    }
                    structural_requirement = Some(index);
                } else if let Some(CFunctionTerminationMeasure::Expression(source)) =
                    &recursive_measure
                {
                    check_expression_measure_recursion(
                        name,
                        source,
                        function,
                        &recursive_callees,
                        &plans,
                        verified_loop_rules.get(name).map_or(&[], Vec::as_slice),
                    )?;
                } else {
                    for member in std::iter::once(name).chain(recursive_callees.iter()) {
                        charge_termination_work(1);
                        let Some(CFunctionTerminationMeasure::NumericParameter(index)) =
                            plans[member].recursive_measure
                        else {
                            return Err(error(
                                "a recursive component cannot mix numeric and structural measures",
                            ));
                        };
                        let parameter =
                            functions[member].parameters().get(index).ok_or_else(|| {
                                error(format!(
                                    "termination parameter index is invalid for `{member}`"
                                ))
                            })?;
                        if parameter.c_type != CType::Int32 {
                            return Err(error(format!(
                                "termination parameter `{}` in `{member}` must have type int32",
                                parameter.name
                            )));
                        }
                        parameter_indices.insert(member.clone(), index);
                    }
                }

                let empty = BTreeMap::new();
                let loop_measures = plan.map_or(&empty, |plan| &plan.loop_measures);
                for measures in loop_measures.values() {
                    let CLoopTerminationMeasure::Ranking(measures) = measures else {
                        continue;
                    };
                    for measure in measures {
                        // A pure component reaches this pass only as the
                        // spelling the plan names it by; the lowered
                        // expression, and so its escape check, lives on the
                        // certified loop head that
                        // `verified_loop_ranking_measures` reads below.
                        let CRankingMeasureKey::CExpression(measure) = measure else {
                            continue;
                        };
                        reject_address_escaped_expression_measure(
                            name,
                            measure,
                            &function.source_body,
                        )?;
                    }
                }
                let certified = match verified_loop_rules.get(name) {
                    Some(rules) => {
                        verified_loop_ranking_measures(name, &function.source_body, rules)?
                    }
                    None => BTreeMap::new(),
                };
                let mut next_loop = 0;
                let mut unranked = Vec::new();
                check_loops(
                    &function.source_body,
                    loop_measures,
                    &certified,
                    name,
                    &mut next_loop,
                    &mut unranked,
                )?;
                if loop_measures.keys().any(|index| *index >= next_loop) {
                    return Err(error(format!(
                        "termination plan for `{name}` refers to a nonexistent loop"
                    )));
                }
                // Only a function certified on its own is known to have had
                // this body executed; a linked body with no rule is not.
                if let Some(rule) = ruled.get(name.as_str()) {
                    let ruled_loops = verified_loop_rules
                        .get(name)
                        .map(|rules| {
                            rules
                                .iter()
                                .filter_map(|rule| rule.loop_index)
                                .collect::<BTreeSet<_>>()
                        })
                        .unwrap_or_default();
                    let executed =
                        loops_executed_to_exit(function, rule.loop_semantics(), &ruled_loops);
                    unranked.retain(|index| !executed.contains(index));
                }
                if let Some(index) = unranked.first() {
                    // An unranked loop is the function's own defect, so it is
                    // reported ahead of anything a callee lacks.
                    refusal = Some(CTerminationRefusal::UnrankedLoop { index: *index });
                }

                if let Some(requirement_index) = structural_requirement {
                    let measure = structural_resource_children(function, requirement_index)?;
                    // An arm the function's own requirements already select is
                    // active on every path; the check reads that from the arm
                    // rather than seeding a synthetic path condition.
                    structural_recursion_paths(
                        &function.source_body,
                        function,
                        &measure,
                        vec![StructuralRecursionPath {
                            aliases: BTreeMap::new(),
                            conditions: Vec::new(),
                        }],
                    )?;
                } else if let Some(index) = parameter_indices.get(name) {
                    let measure = &function.parameters()[*index].name;
                    reject_address_escaped_measure(name, measure, &function.source_body)?;
                    recursion_paths(
                        &function.source_body,
                        measure,
                        &recursive_callees,
                        &parameter_indices,
                        vec![i64::MIN / 2],
                    )?;
                }

                match refusal {
                    Some(refusal) => {
                        refusals.insert(name.clone(), refusal);
                        settled.push(name);
                    }
                    None => {
                        terminating.insert(name.clone());
                    }
                }
            }

            // A recursive edge is sound only if its callee terminates too. Each
            // refused member withdraws the callers that reach it at this height,
            // once per edge, which leaves the largest set whose every call
            // descends.
            while let Some(refused) = settled.pop() {
                charge_termination_work(1);
                for caller in level_callers.remove(refused.as_str()).unwrap_or_default() {
                    charge_termination_work(1);
                    if terminating.remove(caller) {
                        refusals.insert(
                            caller.clone(),
                            CTerminationRefusal::Callee {
                                callee: refused.clone(),
                            },
                        );
                        settled.push(caller);
                    }
                }
            }

            // Only a settled level says whether a declaration was needed. The
            // evidence is withdrawn before any higher caller can read it.
            for name in level {
                charge_termination_work(1);
                if declared_diverging.contains(*name) && terminating.remove(*name) {
                    refusals.insert((*name).clone(), CTerminationRefusal::DeclaredDiverging);
                    unjustified_diverging.push((*name).clone());
                }
            }
        }

        Ok((terminating, refusals, unjustified_diverging))
    };

    // A call through a function pointer reaches some function whose address
    // was taken. The strict walk refuses every such call, so the functions it
    // certifies return without going through any function pointer, in their
    // own bodies or below. When every address taken in this run names one of
    // those, no pointer call can re-enter its caller, and a second walk may
    // let pointer calls return. Otherwise the strict verdicts stand.
    let strict = settle(false)?;
    let mut unsuitable_callbacks = Vec::new();
    for (taker, function) in &functions {
        let mut taken = BTreeSet::new();
        function_address_taken(function, &mut taken);
        for callback in taken {
            charge_termination_work(1);
            // A function this run did not select is an assumption, as
            // everywhere else, even when its unverified body was linked.
            let returns_pointer_free =
                strict.0.contains(&callback) || assumed_terminating.contains(&callback);
            if !returns_pointer_free {
                unsuitable_callbacks.push(CUnsuitableCallback {
                    taker: taker.clone(),
                    callback,
                });
            }
        }
    }
    let makes_pointer_calls = calls
        .values()
        .flatten()
        .any(|callee| callee.ends_with("#indirect"));
    let (terminating, refusals, unjustified_diverging) =
        if makes_pointer_calls && unsuitable_callbacks.is_empty() {
            settle(true)?
        } else {
            strict
        };

    Ok(CTerminationVerdicts {
        rules: partial_rules
            .iter()
            .inspect(|_| charge_termination_work(1))
            .filter(|rule| terminating.contains(rule.function.name()))
            .map(|rule| CVerifiedFunctionTerminationRule {
                function: rule.function.clone(),
            })
            .collect(),
        refusals,
        unjustified_diverging,
        unsuitable_callbacks,
    })
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
            structural_measure: None,
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
    /// A volatile object's value is not a function of the state, so a measure
    /// cannot be read from it, and the refusal says so.
    #[test]
    fn a_measure_may_not_read_a_volatile_object() {
        let state = scalar_state(&[("i", Bitvector32Term::Variable(Variable(1)))]);
        let volatile_read = CExpression::TypedLoad {
            pointer: Box::new(CExpression::Variable("device".to_string())),
            value_type: CType::Int32,
            volatile: true,
            source: CExpressionLoadSource::none(),
        };
        let measures = vec![CRankingComponent::CExpression(CExpression::Subtract(
            Box::new(volatile_read),
            Box::new(CExpression::Variable("i".to_string())),
        ))];
        let error = collect_loop_ranking_obligations(
            &state,
            &state,
            &measures,
            &PureFactContext::default(),
            &mut ExecutionBudget::default(),
        )
        .expect_err("a volatile read has no value at a state");
        assert!(error.contains("volatile"), "{error}");
    }

    #[test]
    fn ranking_members_are_ordered_and_right_nested() {
        let outer = Bitvector32Term::Variable(Variable(1));
        let inner = Bitvector32Term::Variable(Variable(2));
        let entry = scalar_state(&[("i", outer.clone()), ("j", inner.clone())]);
        let post_outer = Bitvector32Term::subtract(outer.clone(), Bitvector32Term::Constant(1));
        let post_inner = Bitvector32Term::add(inner.clone(), Bitvector32Term::Constant(1));
        let back_edge = scalar_state(&[("i", post_outer.clone()), ("j", post_inner.clone())]);
        let measures = vec![
            CRankingComponent::CExpression(CExpression::Variable("i".to_string())),
            CRankingComponent::CExpression(CExpression::Variable("j".to_string())),
        ];
        let obligations = collect_loop_ranking_obligations(
            &back_edge,
            &entry,
            &measures,
            &PureFactContext::default(),
            &mut ExecutionBudget::default(),
        )
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
        let measures = vec![CRankingComponent::CExpression(CExpression::Variable(
            "n".to_string(),
        ))];
        let obligations = collect_loop_ranking_obligations(
            &back_edge,
            &entry,
            &measures,
            &PureFactContext::default(),
            &mut ExecutionBudget::default(),
        )
        .expect("a scalar measure reads at both ends");
        assert_eq!(obligations.len(), 2);
        assert_eq!(
            obligations[1].proposition(),
            &Proposition::ConditionIs(ConditionTerm::signed_less_than(post, value), true)
        );
    }

    fn int32_cell(name: &str) -> Pointer {
        Pointer {
            block: PointerBlock::Concrete(name.to_string()),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    /// A pure component that reads memory: the load is against the state the
    /// component is read at, not a state the surface named.
    fn current_load(cell: &Pointer) -> SpecExpression {
        SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer: Box::new(SpecExpression::Value(CValue::Pointer(CPointerValue::new(
                cell.clone(),
                CType::Int32Pointer,
            )))),
            value_type: CType::Int32,
        }
    }

    /// The surface hands the kernel ONE pure component, and the kernel is what
    /// picks the two states to read it at. Nothing in the declaration names a
    /// state, so the entry and back-edge sides of the decrease member are the
    /// values that one expression takes at the two states it is read at.
    #[test]
    fn a_pure_component_is_read_at_both_states() {
        let cell = int32_cell("counter");
        let value = Bitvector32Term::Variable(Variable(11));
        let post = Bitvector32Term::subtract(value.clone(), Bitvector32Term::Constant(1));
        let mut entry = CState::new();
        entry.memory = CMemory::new().store(cell.clone(), CValue::Int32(value.clone()));
        let mut back_edge = CState::new();
        back_edge.memory = CMemory::new().store(cell.clone(), CValue::Int32(post.clone()));
        let measures = vec![CRankingComponent::Pure {
            source: "count(counter)".to_string(),
            expression: current_load(&cell),
        }];

        let obligations = collect_loop_ranking_obligations(
            &back_edge,
            &entry,
            &measures,
            &PureFactContext::default(),
            &mut ExecutionBudget::default(),
        )
        .expect("a pure measure reads at both ends");

        assert_eq!(obligations.len(), 2);
        assert_eq!(
            obligations[0].proposition(),
            &Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), post.clone()),
                true,
            ),
            "the nonnegativity member reads the back-edge state"
        );
        assert_eq!(
            obligations[1].proposition(),
            &Proposition::ConditionIs(ConditionTerm::signed_less_than(post, value), true),
            "the decrease member compares the back edge against the iteration entry"
        );
        // A pure component has no source spelling of its own once lowered, so
        // the member is named by the spelling the declaration carried.
        assert!(
            obligations[1]
                .context()
                .is_some_and(|context| context.contains("`count(counter)`")),
            "member names the declared component: {:?}",
            obligations[1].context()
        );
    }

    /// The Integer reading of one local, as the Integer carrier's evaluator
    /// produces it.
    fn integer_reading(term: &Bitvector32Term) -> IntegerTerm {
        IntegerTerm::from_machine(MachineIntegerType::Int32, term.clone())
            .expect("an int32 term is a mathematical observation")
    }

    fn current_integer_local(name: &str) -> SpecIntegerExpression {
        SpecIntegerExpression::FromMachine(Box::new(SpecExpression::CExpression(
            CExpression::Variable(name.to_string()),
        )))
    }

    /// An `Integer`-valued component owes the same two members in the other
    /// carrier: `0 <= m` and `m_post < m_pre` as Integer comparisons, built
    /// from the two readings of the one declared component.
    #[test]
    fn an_integer_component_builds_integer_members() {
        let value = Bitvector32Term::Variable(Variable(13));
        let post = Bitvector32Term::subtract(value.clone(), Bitvector32Term::Constant(1));
        let entry = scalar_state(&[("n", value.clone())]);
        let back_edge = scalar_state(&[("n", post.clone())]);
        let measures = vec![CRankingComponent::PureInteger {
            source: "level(n)".to_string(),
            expression: current_integer_local("n"),
        }];

        let obligations = collect_loop_ranking_obligations(
            &back_edge,
            &entry,
            &measures,
            &PureFactContext::default(),
            &mut ExecutionBudget::default(),
        )
        .expect("an Integer measure reads at both ends");

        assert_eq!(obligations.len(), 2);
        assert_eq!(
            obligations[0].proposition(),
            &Proposition::ConditionIs(
                ConditionTerm::integer_less_equal(
                    IntegerTerm::constant_i64(0),
                    integer_reading(&post),
                ),
                true,
            ),
            "the nonnegativity member is an Integer comparison at the back edge"
        );
        assert_eq!(
            obligations[1].proposition(),
            &Proposition::ConditionIs(
                ConditionTerm::integer_less_than(integer_reading(&post), integer_reading(&value)),
                true,
            ),
            "the decrease member is an Integer comparison against the iteration entry"
        );
        assert!(
            obligations[1]
                .context()
                .is_some_and(|context| context.contains("`level(n)`")),
            "member names the declared component: {:?}",
            obligations[1].context()
        );
    }

    /// A tuple may mix carriers. A pivot arm only ever compares one
    /// component's two readings, so each member is built in that component's
    /// own carrier and no comparison crosses them.
    #[test]
    fn a_mixed_tuple_builds_each_member_in_its_own_carrier() {
        let outer = Bitvector32Term::Variable(Variable(17));
        let inner = Bitvector32Term::Variable(Variable(19));
        let post_outer = Bitvector32Term::subtract(outer.clone(), Bitvector32Term::Constant(1));
        let post_inner = Bitvector32Term::subtract(inner.clone(), Bitvector32Term::Constant(1));
        let entry = scalar_state(&[("i", outer.clone()), ("n", inner.clone())]);
        let back_edge = scalar_state(&[("i", post_outer.clone()), ("n", post_inner.clone())]);
        let measures = vec![
            CRankingComponent::CExpression(CExpression::Variable("i".to_string())),
            CRankingComponent::PureInteger {
                source: "level(n)".to_string(),
                expression: current_integer_local("n"),
            },
        ];

        let obligations = collect_loop_ranking_obligations(
            &back_edge,
            &entry,
            &measures,
            &PureFactContext::default(),
            &mut ExecutionBudget::default(),
        )
        .expect("a mixed tuple reads each component in its own carrier");

        assert_eq!(obligations.len(), 3);
        assert_eq!(
            obligations[0].proposition(),
            &Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), post_outer.clone()),
                true,
            )
        );
        assert_eq!(
            obligations[1].proposition(),
            &Proposition::ConditionIs(
                ConditionTerm::integer_less_equal(
                    IntegerTerm::constant_i64(0),
                    integer_reading(&post_inner),
                ),
                true,
            )
        );
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
                ConditionTerm::integer_less_than(
                    integer_reading(&post_inner),
                    integer_reading(&inner),
                ),
                true,
            )),
        );
        assert_eq!(
            obligations[2].proposition(),
            &Proposition::Or(Box::new(pivot_first), Box::new(pivot_second)),
            "the machine pivot stays signed and the Integer pivot stays Integer"
        );
    }

    /// A pure component owes what its reads owe. The loadability obligations
    /// the evaluator raises join the same bundle, ahead of the ranking
    /// members, so the closer discharges them beside the invariants about
    /// those cells rather than the kernel assuming them.
    #[test]
    fn a_pure_component_publishes_its_loadability_obligations() {
        let cell = int32_cell("counter");
        let entry = CState::new();
        let back_edge = CState::new();
        let measures = vec![CRankingComponent::Pure {
            source: "count(counter)".to_string(),
            expression: current_load(&cell),
        }];

        let obligations = collect_loop_ranking_obligations(
            &back_edge,
            &entry,
            &measures,
            &PureFactContext::default(),
            &mut ExecutionBudget::default(),
        )
        .expect("an unknown cell still has a symbolic value");

        let loadable = obligations
            .iter()
            .filter(|obligation| {
                matches!(
                    obligation.proposition(),
                    Proposition::CMemoryLoadable { .. }
                )
            })
            .count();
        assert!(
            loadable > 0,
            "the read's viewability is a member, not an assumption: {:?}",
            obligations
                .iter()
                .map(ProofObligation::proposition)
                .collect::<Vec<_>>()
        );
        assert!(
            obligations[..loadable].iter().all(|obligation| obligation
                .context()
                .is_some_and(|context| context.contains("viewable"))),
            "viewability members come first and say what they are"
        );
        assert_eq!(
            obligations.len(),
            loadable + 2,
            "the ranking members follow the viewability members"
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

#[cfg(test)]
mod local_descent_tests {
    use super::*;
    use std::sync::Arc;

    /// A loop the proof summarized: it carries an invariant, so execution
    /// never ran it to its exit and only a measure can rank it.
    fn summarized_loop(condition: u32) -> CStatement {
        crate::kernel::c_while(
            crate::kernel::c_int32_literal(condition),
            vec![Proposition::ConditionIs(
                ConditionTerm::Constant(true),
                true,
            )],
            CStatement::Skip,
        )
    }

    /// A verified rule whose body calls `callees` in order and then holds the
    /// given loops, which is all the termination check reads of a function.
    fn rule(name: &str, callees: &[&str], loops: usize) -> CVerifiedFunctionRule {
        let mut body = CStatement::Skip;
        for callee in callees {
            body = CStatement::Seq(
                Arc::new(body),
                Arc::new(crate::kernel::c_call(*callee, Vec::new())),
            );
        }
        for _ in 0..loops {
            body = CStatement::Seq(Arc::new(body), Arc::new(summarized_loop(1)));
        }
        CVerifiedFunctionRule {
            function: CFunction::new(CType::Void, name, Vec::new(), body),
            loop_semantics: CLoopSemantics::ApplyVerifiedRules,
        }
    }

    fn check(
        rules: &[CVerifiedFunctionRule],
        plans: &[CFunctionTerminationPlan],
        heights: &BTreeMap<String, usize>,
        assumed: &[&str],
    ) -> Result<CTerminationVerdicts, CTerminationError> {
        c_verified_function_termination_rules(
            rules,
            plans,
            &BTreeMap::new(),
            &[],
            heights,
            &assumed.iter().map(|name| name.to_string()).collect(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
    }

    fn terminating(verdicts: &CTerminationVerdicts) -> BTreeSet<&str> {
        verdicts
            .rules
            .iter()
            .map(|rule| rule.function.name())
            .collect()
    }

    fn heights(entries: &[(&str, usize)]) -> BTreeMap<String, usize> {
        entries
            .iter()
            .map(|(name, height)| (name.to_string(), *height))
            .collect()
    }

    #[test]
    fn planned_heights_follow_the_call_dag_and_share_a_cycle() {
        let rules = [
            rule("top", &["middle", "ping"], 0),
            rule("middle", &["leaf"], 0),
            rule("leaf", &[], 0),
            rule("ping", &["pong"], 0),
            rule("pong", &["ping", "leaf"], 0),
        ];
        assert_eq!(
            c_termination_height_plan(&rules, &[]),
            heights(&[
                ("leaf", 0),
                ("middle", 1),
                ("ping", 1),
                ("pong", 1),
                ("top", 2)
            ])
        );
    }

    #[test]
    fn a_dag_terminates_under_its_planned_heights() {
        let rules = [
            rule("top", &["middle"], 0),
            rule("middle", &["leaf"], 0),
            rule("leaf", &[], 0),
        ];
        let plan = c_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[], &plan, &[]).expect("a consistent plan checks");
        assert_eq!(
            terminating(&verdicts),
            BTreeSet::from(["leaf", "middle", "top"])
        );
        assert!(verdicts.refusals.is_empty());
    }

    /// Heights are untrusted: one that inverts a call is an error, never
    /// evidence.
    #[test]
    fn a_callee_planned_above_its_caller_is_rejected() {
        let rules = [rule("caller", &["callee"], 0), rule("callee", &[], 0)];
        let forged = heights(&[("caller", 0), ("callee", 1)]);
        let error = check(&rules, &[], &forged, &[]).expect_err("an inverted plan must not check");
        assert!(error.message.contains("above its caller"), "{error:?}");
    }

    /// Flattening two functions onto one height hides nothing: the call
    /// between them becomes a recursive edge, which needs a measure.
    #[test]
    fn a_call_between_equal_heights_needs_a_measure() {
        let rules = [rule("caller", &["callee"], 0), rule("callee", &[], 0)];
        let forged = heights(&[("caller", 0), ("callee", 0)]);
        let verdicts = check(&rules, &[], &forged, &[]).expect("the plan is merely unhelpful");
        assert_eq!(terminating(&verdicts), BTreeSet::from(["callee"]));
        assert_eq!(
            verdicts.refusals["caller"],
            CTerminationRefusal::UnmeasuredRecursion {
                callee: "callee".to_string()
            }
        );
    }

    #[test]
    fn a_missing_height_is_rejected() {
        let rules = [rule("only", &[], 0)];
        let error =
            check(&rules, &[], &BTreeMap::new(), &[]).expect_err("every node needs a height");
        assert!(error.message.contains("assigns no height"), "{error:?}");
    }

    #[test]
    fn an_unmeasured_cycle_refuses_its_members_and_their_callers() {
        let rules = [
            rule("top", &["ping"], 0),
            rule("ping", &["pong"], 0),
            rule("pong", &["ping"], 0),
            rule("bystander", &[], 0),
        ];
        let plan = c_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert_eq!(terminating(&verdicts), BTreeSet::from(["bystander"]));
        assert!(matches!(
            verdicts.refusals["ping"],
            CTerminationRefusal::UnmeasuredRecursion { .. }
        ));
        assert_eq!(
            verdicts.refusals["top"],
            CTerminationRefusal::Callee {
                callee: "ping".to_string()
            }
        );
    }

    #[test]
    fn a_callee_outside_the_run_terminates_only_when_assumed() {
        let rules = [rule("caller", &["outside"], 0)];
        let plan = c_termination_height_plan(&rules, &[]);
        let refused = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert_eq!(
            refused.refusals["caller"],
            CTerminationRefusal::Callee {
                callee: "outside".to_string()
            }
        );
        let assumed = check(&rules, &[], &plan, &["outside"]).expect("the plan checks");
        assert_eq!(terminating(&assumed), BTreeSet::from(["caller"]));
    }

    #[test]
    fn a_declared_diverging_function_refuses_its_callers_and_answers_for_the_marker() {
        let rules = [
            rule("caller", &["spins"], 0),
            rule("spins", &[], 1),
            rule("idle", &[], 0),
        ];
        let plan = c_termination_height_plan(&rules, &[]);
        let verdicts = c_verified_function_termination_rules(
            &rules,
            &[],
            &BTreeMap::new(),
            &[],
            &plan,
            &BTreeSet::new(),
            &BTreeSet::from(["spins".to_string(), "idle".to_string()]),
            &BTreeSet::new(),
        )
        .expect("the plan checks");
        assert!(terminating(&verdicts).is_empty());
        // `spins` needs its marker for its loop; `idle` has nothing to justify one.
        assert_eq!(
            verdicts.refusals["spins"],
            CTerminationRefusal::UnrankedLoop { index: 0 }
        );
        assert_eq!(verdicts.unjustified_diverging, ["idle".to_string()]);
        assert_eq!(
            verdicts.refusals["caller"],
            CTerminationRefusal::Callee {
                callee: "spins".to_string()
            }
        );
    }

    /// A measured member of a cycle is locally sound, and still owes its
    /// verdict to the member it calls. When that member is refused for a loop
    /// of its own, the evidence already granted at this height is withdrawn,
    /// whichever of the two the level happened to visit first.
    #[test]
    fn a_refused_cycle_member_withdraws_the_measured_member_that_calls_it() {
        // `void NAME(int32 n) { if (n > 0) { CALLEE(n - 1); } LOOPS }`
        let countdown = |name: &str, callee: &str, loops: usize| {
            let mut body = crate::kernel::c_if(
                crate::kernel::c_greater_than(
                    crate::kernel::c_variable("n"),
                    crate::kernel::c_int32_literal(0),
                ),
                crate::kernel::c_call(
                    callee,
                    vec![crate::kernel::c_subtract(
                        crate::kernel::c_variable("n"),
                        crate::kernel::c_int32_literal(1),
                    )],
                ),
                CStatement::Skip,
            );
            for _ in 0..loops {
                body = CStatement::Seq(Arc::new(body), Arc::new(summarized_loop(1)));
            }
            CVerifiedFunctionRule {
                loop_semantics: CLoopSemantics::ApplyVerifiedRules,
                function: CFunction::new(
                    CType::Void,
                    name,
                    vec![crate::kernel::c_parameter("n", CType::Int32)],
                    body,
                ),
            }
        };
        let measured = |name: &str| CFunctionTerminationPlan {
            function_name: name.to_string(),
            recursive_measure: Some(CFunctionTerminationMeasure::NumericParameter(0)),
            loop_measures: BTreeMap::new(),
        };
        // Both visiting orders: the refused member sorts first, then last.
        for (sound, spins) in [("ping", "a_spins"), ("ping", "z_spins")] {
            let rules = [countdown(sound, spins, 0), countdown(spins, sound, 1)];
            let plan = c_termination_height_plan(&rules, &[]);
            let verdicts = check(&rules, &[measured(sound), measured(spins)], &plan, &[])
                .expect("both recursive edges descend");
            assert!(terminating(&verdicts).is_empty(), "{verdicts:?}");
            assert_eq!(
                verdicts.refusals[spins],
                CTerminationRefusal::UnrankedLoop { index: 0 }
            );
            assert_eq!(
                verdicts.refusals[sound],
                CTerminationRefusal::Callee {
                    callee: spins.to_string()
                }
            );
        }
    }

    /// `loop_at_index` had no arm for a try/catch, so it neither found a loop
    /// inside one nor counted past it, while `check_loops` numbers those
    /// loops. An index then named different source loops in the two walks.
    #[test]
    fn loop_lookup_numbers_loops_inside_try_catch_as_the_check_does() {
        let spin = |condition: u32| {
            crate::kernel::c_while(
                crate::kernel::c_int32_literal(condition),
                Vec::new(),
                CStatement::Skip,
            )
        };
        let body = CStatement::Seq(
            Arc::new(CStatement::TryCatchInt32 {
                try_body: Box::new(spin(1)),
                binding: "code".to_string(),
                handler: Box::new(spin(2)),
                cleanup_unwind: false,
            }),
            Arc::new(spin(3)),
        );

        let mut next_index = 0;
        let mut unranked = Vec::new();
        check_loops(
            &body,
            &BTreeMap::new(),
            &BTreeMap::new(),
            "f",
            &mut next_index,
            &mut unranked,
        )
        .expect("an unranked body checks");
        assert_eq!(unranked, [0, 1, 2]);

        for (index, condition) in [(0, 1), (1, 2), (2, 3)] {
            let found = loop_at_index(&body, index, &mut 0)
                .unwrap_or_else(|| panic!("loop {index} exists"));
            assert!(
                same_statement_shape(found, &spin(condition)),
                "loop {index} must be the loop the check numbered {index}"
            );
        }
        assert!(loop_at_index(&body, 3, &mut 0).is_none());
    }

    /// A rule whose body calls `callees`, calls through the local object
    /// `through` when given one, and takes the address of each of `takes`.
    fn pointer_rule(
        name: &str,
        callees: &[&str],
        through: Option<&str>,
        takes: &[&str],
    ) -> CVerifiedFunctionRule {
        let mut body = CStatement::Skip;
        for callee in callees {
            body = CStatement::Seq(
                Arc::new(body),
                Arc::new(crate::kernel::c_call(*callee, Vec::new())),
            );
        }
        for taken in takes {
            body = CStatement::Seq(
                Arc::new(body),
                Arc::new(CStatement::Assign {
                    name: "slot".to_string(),
                    expression: crate::kernel::c_function_address(*taken),
                }),
            );
        }
        let parameters = match through {
            Some(object) => {
                body = CStatement::Seq(
                    Arc::new(body),
                    Arc::new(crate::kernel::c_call(object, Vec::new())),
                );
                vec![crate::kernel::c_parameter(
                    object,
                    CType::FunctionPointer(CallbackSignature::UNSPECIFIED),
                )]
            }
            None => Vec::new(),
        };
        CVerifiedFunctionRule {
            function: CFunction::new(CType::Void, name, parameters, body),
            loop_semantics: CLoopSemantics::ApplyVerifiedRules,
        }
    }

    /// The ordinary callback: `sort` calls through a pointer, `caller` hands
    /// it `compare`, and `compare` returns without touching a pointer. Every
    /// address taken names such a function, so the pointer call returns.
    #[test]
    fn a_pointer_call_returns_when_every_address_taken_is_pointer_free() {
        let rules = [
            pointer_rule("caller", &["sort"], None, &["compare"]),
            pointer_rule("sort", &[], Some("callback"), &[]),
            pointer_rule("compare", &[], None, &[]),
        ];
        let plan = c_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert_eq!(
            terminating(&verdicts),
            BTreeSet::from(["caller", "compare", "sort"])
        );
        assert!(verdicts.unsuitable_callbacks.is_empty());
    }

    /// `spin` hands itself to `apply`. No direct call closes the cycle, and
    /// the address does: `spin` reaches a pointer call, so it may not be
    /// reached through one, and every pointer call in the run stays refused.
    #[test]
    fn a_function_that_reaches_a_pointer_call_cannot_be_a_callback() {
        let rules = [
            pointer_rule("spin", &["apply"], None, &["spin"]),
            pointer_rule("apply", &[], Some("callback"), &[]),
        ];
        let plan = c_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert!(terminating(&verdicts).is_empty(), "{verdicts:?}");
        assert_eq!(
            verdicts.unsuitable_callbacks,
            [CUnsuitableCallback {
                taker: "spin".to_string(),
                callback: "spin".to_string(),
            }]
        );
        assert_eq!(
            verdicts.refusals["apply"],
            CTerminationRefusal::IndirectCall {
                object: "callback".to_string()
            }
        );
    }

    /// The knot through memory: `install` stores `handler`, `dispatch` calls
    /// what was stored, and `handler` calls `dispatch`. The function that
    /// takes the address never calls through it, so an edge from taker to
    /// callback would miss the cycle. The rule does not: `handler` reaches a
    /// pointer call by way of `dispatch`.
    #[test]
    fn a_stored_callback_cannot_call_back_into_its_dispatcher() {
        let rules = [
            pointer_rule("install", &[], None, &["handler"]),
            pointer_rule("dispatch", &[], Some("stored"), &[]),
            pointer_rule("handler", &["dispatch"], None, &[]),
            pointer_rule("bystander", &[], None, &[]),
        ];
        let plan = c_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        // Taking an address is not a call, so `install` itself returns.
        assert_eq!(
            terminating(&verdicts),
            BTreeSet::from(["bystander", "install"])
        );
        assert_eq!(
            verdicts.unsuitable_callbacks,
            [CUnsuitableCallback {
                taker: "install".to_string(),
                callback: "handler".to_string(),
            }]
        );
    }

    /// A callback with an unranked loop, or one declared diverging, is not
    /// shown to return at all, so it is no more suitable than one that
    /// reaches a pointer call.
    #[test]
    fn a_callback_without_evidence_keeps_pointer_calls_refused() {
        let rules = [
            pointer_rule("caller", &["apply"], None, &["loops"]),
            pointer_rule("apply", &[], Some("callback"), &[]),
            rule("loops", &[], 1),
        ];
        let plan = c_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert!(terminating(&verdicts).is_empty(), "{verdicts:?}");
        assert_eq!(verdicts.unsuitable_callbacks.len(), 1);
        assert_eq!(
            verdicts.refusals["loops"],
            CTerminationRefusal::UnrankedLoop { index: 0 }
        );
    }

    /// No address is taken here, so nothing refuses the pointer call for a
    /// callback of this run's. The contract the caller requires is then the
    /// whole of what the call may assume, and it is declared `diverges`, so
    /// the call admits an implementation that never returns. `applies` is
    /// refused for it whether or not it says `diverges` itself; saying so
    /// justifies the marker rather than certifying the function.
    #[test]
    fn a_diverging_named_contract_refuses_the_pointer_call_that_applies_it() {
        let mut applies = pointer_rule("applies", &[], Some("callback"), &[]);
        applies
            .function
            .contract_interface
            .contract_requires
            .push(SpecProposition::Predicate {
                name: CFunctionContract::predicate_name_for("Spinner"),
                arguments: vec![SpecPredicateArgument::Value(SpecExpression::CExpression(
                    CExpression::Variable("callback".to_string()),
                ))],
            });
        let rules = [pointer_rule("caller", &["applies"], None, &[]), applies];
        let plan = c_termination_height_plan(&rules, &[]);
        let contracts = BTreeSet::from(["Spinner".to_string()]);

        // A contract with no marker leaves the pointer call authorized.
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert_eq!(
            terminating(&verdicts),
            BTreeSet::from(["applies", "caller"])
        );

        let verdicts = c_verified_function_termination_rules(
            &rules,
            &[],
            &BTreeMap::new(),
            &[],
            &plan,
            &BTreeSet::new(),
            &BTreeSet::new(),
            &contracts,
        )
        .expect("the plan checks");
        assert!(terminating(&verdicts).is_empty(), "{verdicts:?}");
        assert_eq!(
            verdicts.refusals["applies"],
            CTerminationRefusal::DivergingContract {
                object: "callback".to_string(),
                contract: "Spinner".to_string(),
            }
        );
        assert_eq!(
            verdicts.refusals["caller"],
            CTerminationRefusal::Callee {
                callee: "applies".to_string()
            }
        );
        assert!(verdicts.unjustified_diverging.is_empty());

        // The marker on `applies` answers for exactly this call, so it is
        // needed, not redundant.
        let verdicts = c_verified_function_termination_rules(
            &rules,
            &[],
            &BTreeMap::new(),
            &[],
            &plan,
            &BTreeSet::new(),
            &BTreeSet::from(["applies".to_string()]),
            &contracts,
        )
        .expect("the plan checks");
        assert_eq!(
            verdicts.refusals["applies"],
            CTerminationRefusal::DivergingContract {
                object: "callback".to_string(),
                contract: "Spinner".to_string(),
            }
        );
        assert!(verdicts.unjustified_diverging.is_empty());
    }

    /// A loop with no annotation has one route through execution, the
    /// concrete one, which returns only when every feasible path has left the
    /// loop. A function certified with such a loop ran it to its exit, so it
    /// owes no measure; the same loop in a linked body nobody certified, or a
    /// loop the proof summarized, still does.
    #[test]
    fn a_loop_certification_executed_to_its_exit_owes_no_measure() {
        let bare = |name: &str| CVerifiedFunctionRule {
            loop_semantics: CLoopSemantics::ApplyVerifiedRules,
            function: CFunction::new(
                CType::Void,
                name,
                Vec::new(),
                crate::kernel::c_while(
                    crate::kernel::c_int32_literal(0),
                    Vec::new(),
                    CStatement::Skip,
                ),
            ),
        };
        let rules = [bare("counts"), rule("summarized", &[], 1)];
        let plan = c_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert_eq!(terminating(&verdicts), BTreeSet::from(["counts"]));
        assert_eq!(
            verdicts.refusals["summarized"],
            CTerminationRefusal::UnrankedLoop { index: 0 }
        );

        // The same bare loop in a body with no rule of its own: a helper the
        // verified caller reaches.
        let helper = bare("helper").function.with_inline_body();
        let caller = [rule("caller", &["helper"], 0)];
        let bodies = [&helper];
        let plan = c_termination_height_plan(&caller, &bodies);
        let verdicts = c_verified_function_termination_rules(
            &caller,
            &[],
            &BTreeMap::new(),
            &bodies,
            &plan,
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .expect("the plan checks");
        assert_eq!(
            verdicts.refusals["helper"],
            CTerminationRefusal::UnrankedLoop { index: 0 }
        );
    }

    /// A loop whose only annotation is the inherited frame check ran
    /// concretely if the rule was certified under `ApplyVerifiedRules` and no
    /// loop rule names it; certified under `Verify` it may have been
    /// summarized, and a loop a rule names was.
    #[test]
    fn a_frame_checked_loop_is_granted_only_from_a_concrete_certification() {
        let framed = crate::kernel::c_while_with_invariant_and_effect_checks(
            crate::kernel::c_int32_literal(0),
            Vec::new(),
            Vec::new(),
            vec![crate::kernel::CLoopEffectCheck::new_with_origin(
                crate::kernel::CLoopEffect::Mutable(Vec::new()),
                crate::kernel::CLoopEffectSpan::Whole,
                CLoopEffectOrigin::InheritedResourceDerived,
                None,
            )],
            CStatement::Skip,
        );
        let function = CFunction::new(CType::Void, "f", Vec::new(), framed);
        let none = BTreeSet::new();
        assert_eq!(
            loops_executed_to_exit(&function, CLoopSemantics::ApplyVerifiedRules, &none),
            BTreeSet::from([0])
        );
        assert!(loops_executed_to_exit(&function, CLoopSemantics::Verify, &none).is_empty());
        assert!(
            loops_executed_to_exit(
                &function,
                CLoopSemantics::ApplyVerifiedRules,
                &BTreeSet::from([0])
            )
            .is_empty()
        );
        let explicit = crate::kernel::c_while_with_invariant_and_effect_checks(
            crate::kernel::c_int32_literal(0),
            Vec::new(),
            Vec::new(),
            vec![crate::kernel::CLoopEffectCheck::new_with_origin(
                crate::kernel::CLoopEffect::Mutable(Vec::new()),
                crate::kernel::CLoopEffectSpan::Whole,
                CLoopEffectOrigin::Explicit,
                None,
            )],
            CStatement::Skip,
        );
        let function = CFunction::new(CType::Void, "f", Vec::new(), explicit);
        assert!(
            loops_executed_to_exit(&function, CLoopSemantics::ApplyVerifiedRules, &none).is_empty()
        );
    }

    /// The indices name source loops, so nothing is granted when the
    /// certified body's loops are not the source body's loops.
    #[test]
    fn executed_loops_are_granted_only_when_the_bodies_agree() {
        let spin = |condition: u32| {
            crate::kernel::c_while(
                crate::kernel::c_int32_literal(condition),
                Vec::new(),
                CStatement::Skip,
            )
        };
        let agrees = CFunction::new(CType::Void, "f", Vec::new(), spin(0));
        assert_eq!(
            loops_executed_to_exit(&agrees, CLoopSemantics::Verify, &BTreeSet::new()),
            BTreeSet::from([0])
        );
        let differs =
            CFunction::new(CType::Void, "f", Vec::new(), spin(0)).with_source_body(spin(1));
        assert!(
            loops_executed_to_exit(&differs, CLoopSemantics::Verify, &BTreeSet::new()).is_empty()
        );
        let summarized = CFunction::new(CType::Void, "f", Vec::new(), summarized_loop(0))
            .with_source_body(spin(0));
        assert!(
            loops_executed_to_exit(&summarized, CLoopSemantics::Verify, &BTreeSet::new())
                .is_empty()
        );
    }

    /// Each sequential `if` used to double the list of path bounds the
    /// recursion checker carried, so a recursive function with a few dozen
    /// of them before its ranked call could not be checked at all. The list
    /// now holds one bound per join, which decides every edge the same way.
    #[test]
    fn a_recursion_check_is_linear_in_sequential_branches() {
        let n = || crate::kernel::c_variable("n");
        let literal = |value: u32| crate::kernel::c_int32_literal(value);
        let guarded_call = |argument: CExpression| {
            crate::kernel::c_if(
                crate::kernel::c_greater_than(n(), literal(0)),
                crate::kernel::c_call("countdown", vec![argument]),
                CStatement::Skip,
            )
        };
        // A balanced sequence, so the walk's depth is logarithmic and the
        // test measures the branch count and not the nesting.
        fn sequence(statements: &[CStatement]) -> CStatement {
            match statements {
                [] => CStatement::Skip,
                [only] => only.clone(),
                _ => {
                    let (left, right) = statements.split_at(statements.len() / 2);
                    CStatement::Seq(Arc::new(sequence(left)), Arc::new(sequence(right)))
                }
            }
        }
        let build = |branches: usize, descends: bool| {
            // Branches on the measure that establish nothing about it.
            let branches = (0..branches)
                .map(|index| {
                    crate::kernel::c_if(
                        crate::kernel::c_less_than(n(), literal(index as u32 + 1_000)),
                        CStatement::Skip,
                        CStatement::Skip,
                    )
                })
                .collect::<Vec<_>>();
            let mut body = sequence(&branches);
            let argument = if descends {
                crate::kernel::c_subtract(n(), literal(1))
            } else {
                n()
            };
            body = CStatement::Seq(Arc::new(body), Arc::new(guarded_call(argument)));
            [CVerifiedFunctionRule {
                loop_semantics: CLoopSemantics::ApplyVerifiedRules,
                function: CFunction::new(
                    CType::Void,
                    "countdown",
                    vec![crate::kernel::c_parameter("n", CType::Int32)],
                    body,
                ),
            }]
        };
        let plan = CFunctionTerminationPlan {
            function_name: "countdown".to_string(),
            recursive_measure: Some(CFunctionTerminationMeasure::NumericParameter(0)),
            loop_measures: BTreeMap::new(),
        };
        for branches in [8, 64, 512] {
            let rules = build(branches, true);
            let heights = c_termination_height_plan(&rules, &[]);
            let started = std::time::Instant::now();
            let verdicts = check(&rules, std::slice::from_ref(&plan), &heights, &[])
                .expect("a descending call checks");
            assert_eq!(terminating(&verdicts), BTreeSet::from(["countdown"]));
            assert!(
                started.elapsed() < std::time::Duration::from_secs(5),
                "{branches} sequential branches must not take {:?}",
                started.elapsed()
            );
        }
        let rules = build(64, false);
        let heights = c_termination_height_plan(&rules, &[]);
        let error = check(&rules, std::slice::from_ref(&plan), &heights, &[])
            .expect_err("a call that passes the measure unchanged does not descend");
        assert!(error.message.contains("must pass"), "{error:?}");
    }

    /// `realloc` is modeled by execution itself, so it is no node of the call
    /// graph and needs no assumption to return.
    #[test]
    fn the_modeled_realloc_returns_without_being_assumed() {
        let rules = [rule("grows", &["realloc"], 0)];
        let plan = c_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert_eq!(terminating(&verdicts), BTreeSet::from(["grows"]));
        assert!(verdicts.refusals.is_empty());
    }

    /// An unranked loop used to stop the walk, so later loops were never
    /// counted and a measure planned for one of them was reported as naming a
    /// loop that does not exist.
    #[test]
    fn an_unranked_loop_does_not_hide_the_loops_after_it() {
        let rules = [rule("two_loops", &[], 2)];
        let plan = c_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert_eq!(
            verdicts.refusals["two_loops"],
            CTerminationRefusal::UnrankedLoop { index: 0 }
        );

        let mut ranks_second = CFunctionTerminationPlan {
            function_name: "two_loops".to_string(),
            recursive_measure: None,
            loop_measures: BTreeMap::new(),
        };
        ranks_second.extend_loop_measures([(
            1,
            CLoopTerminationMeasure::Ranking(vec![CRankingMeasureKey::CExpression(
                CExpression::Variable("n".to_string()),
            )]),
        )]);
        let error = check(&rules, &[ranks_second], &plan, &[])
            .expect_err("loop 1 is planned but was never certified");
        assert!(
            error.message.contains("no verified loop rule"),
            "loop 1 exists and must be reported as uncertified, got {error:?}"
        );
    }

    /// The planner keeps its own stack, and the check visits each function
    /// once, so a call chain as long as the project is neither a machine
    /// stack overflow nor a quadratic walk.
    #[test]
    fn a_long_call_chain_plans_and_checks() {
        const LENGTH: usize = 20_000;
        let name = |index: usize| format!("f{index:05}");
        let rules = (0..LENGTH)
            .map(|index| {
                if index + 1 < LENGTH {
                    rule(&name(index), &[&name(index + 1)], 0)
                } else {
                    rule(&name(index), &[], 0)
                }
            })
            .collect::<Vec<_>>();
        let plan = c_termination_height_plan(&rules, &[]);
        assert_eq!(plan[&name(0)], LENGTH - 1);
        assert_eq!(plan[&name(LENGTH - 1)], 0);
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert_eq!(verdicts.rules.len(), LENGTH);
    }

    /// A rule for a self-recursive `name` that also calls each of `callees`,
    /// carrying the declared measure on its contract interface when `measure`
    /// says so. `inline` makes the body a header-provided inline helper.
    fn recursive_rule(
        name: &str,
        callees: &[&str],
        measure: bool,
        inline: bool,
        in_loop: bool,
    ) -> CVerifiedFunctionRule {
        let mut body = CStatement::Skip;
        for callee in std::iter::once(&name).chain(callees) {
            let call = crate::kernel::c_call(*callee, Vec::new());
            let call = if in_loop {
                crate::kernel::c_while(crate::kernel::c_int32_literal(1), Vec::new(), call)
            } else {
                call
            };
            body = CStatement::Seq(Arc::new(body), Arc::new(call));
        }
        let mut function = CFunction::new(CType::Void, name, Vec::new(), body);
        if measure {
            function = function.with_recursion_measure(CRankingComponent::Pure {
                source: "level(n)".to_string(),
                expression: SpecExpression::CExpression(CExpression::Variable("n".to_string())),
            });
        }
        if inline {
            function = function.with_inline_body();
        }
        CVerifiedFunctionRule {
            function,
            loop_semantics: CLoopSemantics::ApplyVerifiedRules,
        }
    }

    fn expression_plan(name: &str) -> CFunctionTerminationPlan {
        CFunctionTerminationPlan {
            function_name: name.to_string(),
            recursive_measure: Some(CFunctionTerminationMeasure::Expression(
                "level(n)".to_string(),
            )),
            loop_measures: BTreeMap::new(),
        }
    }

    /// The expression measure certifies direct self-recursion. Nothing about
    /// the body is analysed: the descent rides on obligations the call steps
    /// raised while this rule was being certified.
    #[test]
    fn an_expression_measure_ranks_direct_self_recursion() {
        let rules = [recursive_rule("drain", &[], true, false, false)];
        let plan = c_termination_height_plan(&rules, &[]);
        let verdicts =
            check(&rules, &[expression_plan("drain")], &plan, &[]).expect("the plan checks");
        assert_eq!(terminating(&verdicts), BTreeSet::from(["drain"]));
    }

    /// The plan is untrusted. A plan claiming an expression measure for a
    /// function whose certified interface declares none is a plan for
    /// obligations no call step emitted.
    #[test]
    fn an_expression_plan_without_a_declared_measure_is_rejected() {
        let rules = [recursive_rule("drain", &[], false, false, false)];
        let plan = c_termination_height_plan(&rules, &[]);
        let error = check(&rules, &[expression_plan("drain")], &plan, &[])
            .expect_err("an undeclared measure must not check");
        assert!(
            error.message.contains("carries no declared measure"),
            "{error:?}"
        );
    }

    /// The anchor names one function, so a second member of the cycle owes
    /// nothing. Slice 1 refuses such a component rather than certifying a
    /// recursion with an unranked edge.
    #[test]
    fn an_expression_measure_refuses_a_mutually_recursive_component() {
        let rules = [
            recursive_rule("even", &["odd"], true, false, false),
            recursive_rule("odd", &["even"], true, false, false),
        ];
        let heights = heights(&[("even", 0), ("odd", 0)]);
        let error = check(
            &rules,
            &[expression_plan("even"), expression_plan("odd")],
            &heights,
            &[],
        )
        .expect_err("a two-function cycle must not check");
        assert!(
            error.message.contains("recursive component with"),
            "{error:?}"
        );
    }

    /// An inline body executes at the call site instead of applying a
    /// contract, so no call step reads the anchor and no descent is ever
    /// owed.
    #[test]
    fn an_expression_measure_refuses_an_inline_bodied_helper() {
        let rules = [recursive_rule("drain", &[], true, true, false)];
        let plan = c_termination_height_plan(&rules, &[]);
        let error = check(&rules, &[expression_plan("drain")], &plan, &[])
            .expect_err("an inline self-recursive helper must not check");
        assert!(error.message.contains("inline body"), "{error:?}");
    }

    /// The `decreases` component `recursive_rule` declares, which is also the
    /// one its ranked loop is ranked by.
    fn declared_component() -> CRankingComponent {
        CRankingComponent::Pure {
            source: "level(n)".to_string(),
            expression: SpecExpression::CExpression(CExpression::Variable("n".to_string())),
        }
    }

    /// A rule for `drain`, whose self-call sits inside one summarized loop
    /// ranked by the same component. `loop_measures` is the plan side of that
    /// ranking, so the two agree and the loop is not refused as unranked.
    fn self_call_in_loop_rule(name: &str) -> CVerifiedFunctionRule {
        let body = CStatement::Seq(
            Arc::new(CStatement::Skip),
            Arc::new(CStatement::While {
                condition: crate::kernel::c_int32_literal(1),
                invariant: vec![Proposition::ConditionIs(
                    ConditionTerm::Constant(true),
                    true,
                )],
                invariant_checks: Vec::new(),
                effect_checks: Vec::new(),
                resource_specs: Vec::new(),
                ranking_measures: vec![declared_component()],
                structural_measure: None,
                do_while: false,
                body: Box::new(crate::kernel::c_call(name, Vec::new())),
            }),
        );
        CVerifiedFunctionRule {
            function: CFunction::new(CType::Void, name, Vec::new(), body)
                .with_recursion_measure(declared_component()),
            loop_semantics: CLoopSemantics::ApplyVerifiedRules,
        }
    }

    /// The plan for [`self_call_in_loop_rule`]: the expression measure for the
    /// recursion, and the same component as loop 0's own ranking.
    fn self_call_in_loop_plan(name: &str) -> CFunctionTerminationPlan {
        CFunctionTerminationPlan {
            loop_measures: BTreeMap::from([(
                0,
                CLoopTerminationMeasure::Ranking(vec![declared_component().key()]),
            )]),
            ..expression_plan(name)
        }
    }

    /// The certified rule for that loop, carrying `anchor`.
    ///
    /// Only the kernel writes `recursion_anchor`, from the environment the
    /// paths were produced in; the struct is assembled directly here because
    /// this test is inside the kernel.
    fn loop_rule_for(function: &CFunction, anchor: Option<CRecursionAnchor>) -> CVerifiedLoopRule {
        let CStatement::Seq(_, loop_statement) = &function.source_body else {
            unreachable!("`self_call_in_loop_rule` builds a sequence");
        };
        CVerifiedLoopRule {
            symbolic_entry_state: CState::default(),
            loop_statement: loop_statement.as_ref().clone(),
            loop_index: Some(0),
            required_assumptions: PureFactContext::new(),
            paths: Vec::new(),
            composite_resource_definitions: Vec::new(),
            recursion_anchor: anchor.map(Arc::new),
        }
    }

    fn anchor_for(name: &str) -> CRecursionAnchor {
        CRecursionAnchor {
            function: name.to_string(),
            component: declared_component(),
            measure: CRankingMeasureValue::Machine(Bitvector32Term::Constant(7)),
            entry_obligations: Vec::new(),
        }
    }

    fn check_with_loop_rules(
        rules: &[CVerifiedFunctionRule],
        plans: &[CFunctionTerminationPlan],
        loop_rules: &BTreeMap<String, Vec<CVerifiedLoopRule>>,
    ) -> Result<CTerminationVerdicts, CTerminationError> {
        c_verified_function_termination_rules(
            rules,
            plans,
            loop_rules,
            &[],
            &c_termination_height_plan(rules, &[]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
    }

    /// A loop is verified once and then applied as a summary, so the descent
    /// at a self-call inside it is owed by the loop's own judgment. A rule
    /// certified under this function's anchor is one whose body raised those
    /// obligations, and the summary exists only because they were discharged.
    #[test]
    fn an_expression_measure_ranks_a_self_call_under_an_anchored_loop() {
        let rules = [self_call_in_loop_rule("drain")];
        let loop_rules = BTreeMap::from([(
            "drain".to_string(),
            vec![loop_rule_for(&rules[0].function, Some(anchor_for("drain")))],
        )]);
        let verdicts =
            check_with_loop_rules(&rules, &[self_call_in_loop_plan("drain")], &loop_rules)
                .expect("the plan checks");
        assert_eq!(terminating(&verdicts), BTreeSet::from(["drain"]));
    }

    /// Without the anchor the loop's body raised no descent obligation, so
    /// the summary answers for a call that was never ranked. The judgment
    /// reads the certified rule, not the plan, and refuses it by name.
    #[test]
    fn an_expression_measure_refuses_a_self_call_under_an_unanchored_loop() {
        let rules = [self_call_in_loop_rule("drain")];
        let loop_rules = BTreeMap::from([(
            "drain".to_string(),
            vec![loop_rule_for(&rules[0].function, None)],
        )]);
        let error = check_with_loop_rules(&rules, &[self_call_in_loop_plan("drain")], &loop_rules)
            .expect_err("an unanchored loop rule must not check");
        assert!(
            error
                .message
                .contains("certified without `drain`'s recursion anchor"),
            "{error:?}"
        );
    }

    /// An anchor for another function, or for another measure, ranks nothing
    /// here: the judgment binds the anchor to this certified function and the
    /// measure its own interface declares.
    #[test]
    fn a_loop_anchored_for_another_function_does_not_rank_this_recursion() {
        let rules = [self_call_in_loop_rule("drain")];
        let loop_rules = BTreeMap::from([(
            "drain".to_string(),
            vec![loop_rule_for(&rules[0].function, Some(anchor_for("other")))],
        )]);
        let error = check_with_loop_rules(&rules, &[self_call_in_loop_plan("drain")], &loop_rules)
            .expect_err("an anchor for another function must not check");
        assert!(
            error
                .message
                .contains("certified without `drain`'s recursion anchor"),
            "{error:?}"
        );
    }

    /// With no verified rule at all there is no loop judgment that could have
    /// owed the descent, and the self-call is refused for the same reason.
    #[test]
    fn an_expression_measure_refuses_a_self_call_under_an_uncertified_loop() {
        let rules = [recursive_rule("drain", &[], true, false, true)];
        let error = check_with_loop_rules(&rules, &[expression_plan("drain")], &BTreeMap::new())
            .expect_err("a self-call under a loop with no rule must not check");
        assert!(
            error
                .message
                .contains("certified without `drain`'s recursion anchor"),
            "{error:?}"
        );
    }

    /// `decreases <parameter>` is untouched: it still resolves the index
    /// against the verified function and analyses the recursion paths.
    #[test]
    fn a_parameter_measure_is_unaffected_by_a_declared_expression_measure() {
        let rules = [recursive_rule("drain", &[], false, false, false)];
        let plan = c_termination_height_plan(&rules, &[]);
        let numeric = CFunctionTerminationPlan {
            function_name: "drain".to_string(),
            recursive_measure: Some(CFunctionTerminationMeasure::NumericParameter(0)),
            loop_measures: BTreeMap::new(),
        };
        let error = check(&rules, &[numeric], &plan, &[])
            .expect_err("`drain` has no parameter to rank, as before");
        assert!(
            error
                .message
                .contains("termination parameter index is invalid"),
            "{error:?}"
        );
    }
}

/// Deterministic scaling regressions for the termination check and its height
/// planner.
///
/// The contract these pin is in `docs/internals/verification-efficiency.md`:
/// planning and checking cost the call-graph nodes and edges of the selected
/// run, not a search over it. Every sample counts cooperative verifier
/// checkpoints rather than host time, so the curve is the same on any machine
/// under any load.
#[cfg(test)]
mod termination_scaling_tests {
    use super::*;
    use std::sync::Arc;

    /// Four geometric sizes give three adjacent ratios. Work linear in nodes
    /// and edges, up to the BTree indexing factor, doubles; holding every
    /// ratio under this rejects the 4x-per-doubling curve of a quadratic
    /// checker, which is what the pairwise-reachability predecessor of the
    /// local-descent check had.
    const MAX_GROWTH_RATIO: usize = 3;

    const SIZES: [usize; 4] = [500, 1_000, 2_000, 4_000];

    /// A call sequence built as a balanced tree rather than a left spine.
    /// `Seq` is associative, so this is the same body with the same call
    /// sites; only its nesting depth changes. The termination walks are
    /// recursive, so a 4,000-call fan-out root built as a spine would measure
    /// the host's stack rather than the checker's work.
    fn calls_body(callees: &[String]) -> CStatement {
        match callees {
            [] => CStatement::Skip,
            [only] => crate::kernel::c_call(only.clone(), Vec::new()),
            _ => {
                let (left, right) = callees.split_at(callees.len() / 2);
                CStatement::Seq(Arc::new(calls_body(left)), Arc::new(calls_body(right)))
            }
        }
    }

    /// A verified rule whose body calls `callees` and nothing else, which is
    /// all the termination check reads of a function carrying no loops and no
    /// measures.
    fn rule(name: &str, callees: &[String]) -> CVerifiedFunctionRule {
        CVerifiedFunctionRule {
            function: CFunction::new(CType::Void, name, Vec::new(), calls_body(callees)),
            loop_semantics: CLoopSemantics::ApplyVerifiedRules,
        }
    }

    /// One shape at one size: the deterministic work the planner and then the
    /// check spent on it.
    #[derive(Clone, Debug)]
    struct Sample {
        size: usize,
        nodes: usize,
        plan_work: usize,
        check_work: usize,
    }

    /// Plans heights, checks them, and hands the verdicts to `inspect`, so a
    /// curve cannot be flattened by a run that decides nothing.
    fn sample(
        size: usize,
        rules: &[CVerifiedFunctionRule],
        inspect: impl FnOnce(&BTreeMap<String, usize>, &CTerminationVerdicts),
    ) -> Sample {
        let (heights, plan_work) = crate::instrumentation::measure_deterministic_work(|| {
            c_termination_height_plan(rules, &[])
        });
        let (verdicts, check_work) = crate::instrumentation::measure_deterministic_work(|| {
            c_verified_function_termination_rules(
                rules,
                &[],
                &BTreeMap::new(),
                &[],
                &heights,
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
            )
            .expect("a planned height assignment checks")
        });
        assert_eq!(
            verdicts.rules.len() + verdicts.refusals.len(),
            rules.len(),
            "every function receives evidence or a reason"
        );
        inspect(&heights, &verdicts);
        Sample {
            size,
            nodes: rules.len(),
            plan_work,
            check_work,
        }
    }

    fn assert_near_linear(shape: &str, samples: &[Sample]) {
        assert_eq!(samples.len(), SIZES.len());
        for pair in samples.windows(2) {
            assert_eq!(
                pair[1].size,
                pair[0].size * 2,
                "{shape}: sizes must double: {samples:?}"
            );
            assert!(
                pair[1].plan_work <= pair[0].plan_work * MAX_GROWTH_RATIO,
                "{shape}: height planning grows faster than its node-and-edge contract: {samples:?}"
            );
            assert!(
                pair[1].check_work <= pair[0].check_work * MAX_GROWTH_RATIO,
                "{shape}: the termination check grows faster than its node-and-edge contract: {samples:?}"
            );
        }
    }

    /// The deepest graph: height equals the node count, so every level holds
    /// one function and the check settles `n` levels in ascending order.
    #[test]
    fn one_long_call_chain_costs_linear_termination_work() {
        let name = |index: usize| format!("chain{index:06}");
        let mut samples = Vec::new();
        for size in SIZES {
            let rules = (0..size)
                .map(|index| {
                    let callees = if index + 1 < size {
                        vec![name(index + 1)]
                    } else {
                        Vec::new()
                    };
                    rule(&name(index), &callees)
                })
                .collect::<Vec<_>>();
            samples.push(sample(size, &rules, |heights, verdicts| {
                assert_eq!(heights[&name(0)], size - 1);
                assert_eq!(heights[&name(size - 1)], 0);
                assert_eq!(verdicts.rules.len(), size, "a call chain all terminates");
                assert!(verdicts.refusals.is_empty());
            }));
        }
        report("call chain", &samples);
        assert_near_linear("call chain", &samples);
    }

    /// The widest graph: one level of `n` leaves, and a root whose own call
    /// list is the whole edge set.
    #[test]
    fn wide_fan_out_costs_linear_termination_work() {
        let leaf = |index: usize| format!("leaf{index:06}");
        let mut samples = Vec::new();
        for size in SIZES {
            let leaves = (0..size).map(leaf).collect::<Vec<_>>();
            let mut rules = vec![rule("root", &leaves)];
            rules.extend(leaves.iter().map(|name| rule(name, &[])));
            samples.push(sample(size, &rules, |heights, verdicts| {
                assert_eq!(heights["root"], 1);
                assert_eq!(heights[&leaf(0)], 0);
                assert_eq!(
                    verdicts.rules.len(),
                    size + 1,
                    "a root over terminating leaves terminates"
                );
                assert!(verdicts.refusals.is_empty());
            }));
        }
        report("wide fan-out", &samples);
        assert_near_linear("wide fan-out", &samples);
    }

    /// Many two-member cycles, each with its own caller. Every cycle member is
    /// refused for unmeasured recursion, every refusal is pushed through the
    /// level worklist, and every caller then reads a refused callee.
    #[test]
    fn many_small_unmeasured_cycles_cost_linear_termination_work() {
        let ping = |index: usize| format!("ping{index:06}");
        let pong = |index: usize| format!("pong{index:06}");
        let caller = |index: usize| format!("caller{index:06}");
        let mut samples = Vec::new();
        for size in SIZES {
            let groups = size / 2;
            let mut rules = Vec::new();
            for index in 0..groups {
                rules.push(rule(&ping(index), &[pong(index)]));
                rules.push(rule(&pong(index), &[ping(index)]));
                rules.push(rule(&caller(index), &[ping(index)]));
            }
            samples.push(sample(size, &rules, |heights, verdicts| {
                assert_eq!(heights[&ping(0)], 0, "a cycle's members share a height");
                assert_eq!(heights[&pong(0)], 0);
                assert_eq!(heights[&caller(0)], 1);
                assert!(verdicts.rules.is_empty(), "nothing here terminates");
                for index in [0, groups - 1] {
                    assert!(matches!(
                        verdicts.refusals[&ping(index)],
                        CTerminationRefusal::UnmeasuredRecursion { .. }
                    ));
                    assert!(matches!(
                        verdicts.refusals[&pong(index)],
                        CTerminationRefusal::UnmeasuredRecursion { .. }
                    ));
                    assert_eq!(
                        verdicts.refusals[&caller(index)],
                        CTerminationRefusal::Callee {
                            callee: ping(index)
                        }
                    );
                }
            }));
        }
        report("many small unmeasured cycles", &samples);
        assert_near_linear("many small unmeasured cycles", &samples);
    }

    /// One strongly connected component of `n` functions: the planner's
    /// explicit stack holds every member at once, and the check settles them
    /// as a single level.
    #[test]
    fn one_large_cycle_costs_linear_termination_work() {
        let name = |index: usize| format!("ring{index:06}");
        let mut samples = Vec::new();
        for size in SIZES {
            let rules = (0..size)
                .map(|index| rule(&name(index), &[name((index + 1) % size)]))
                .collect::<Vec<_>>();
            samples.push(sample(size, &rules, |heights, verdicts| {
                assert!(
                    (0..size).all(|index| heights[&name(index)] == 0),
                    "one cycle is one level"
                );
                assert!(verdicts.rules.is_empty());
                assert!(
                    (0..size).all(|index| matches!(
                        verdicts.refusals[&name(index)],
                        CTerminationRefusal::UnmeasuredRecursion { .. }
                    )),
                    "every member of an unmeasured cycle is refused for it"
                );
            }));
        }
        report("one large cycle", &samples);
        assert_near_linear("one large cycle", &samples);
    }

    /// A layered DAG whose edges outnumber its nodes four to one, so a check
    /// linear in edges and one linear only in nodes are distinguishable.
    #[test]
    fn a_layered_dag_costs_linear_termination_work() {
        const WIDTH: usize = 8;
        const FAN_OUT: usize = 4;
        let name = |layer: usize, index: usize| format!("dag{layer:06}_{index}");
        let mut samples = Vec::new();
        for size in SIZES {
            let layers = size.div_ceil(WIDTH);
            let nodes = layers * WIDTH;
            let mut rules = Vec::new();
            for layer in 0..layers {
                for index in 0..WIDTH {
                    let callees = if layer + 1 < layers {
                        (0..FAN_OUT)
                            .map(|step| name(layer + 1, (index + step) % WIDTH))
                            .collect::<Vec<_>>()
                    } else {
                        Vec::new()
                    };
                    rules.push(rule(&name(layer, index), &callees));
                }
            }
            assert_eq!(rules.len(), nodes);
            samples.push(sample(size, &rules, |heights, verdicts| {
                assert_eq!(heights[&name(0, 0)], layers - 1, "the top layer is deepest");
                assert_eq!(heights[&name(layers - 1, 0)], 0);
                assert_eq!(verdicts.rules.len(), nodes, "a DAG all terminates");
                assert!(verdicts.refusals.is_empty());
            }));
        }
        report("layered DAG", &samples);
        assert_near_linear("layered DAG", &samples);
    }

    /// The measured curve, so the numbers quoted in
    /// `docs/internals/verification-efficiency.md` can be reproduced with
    /// `cargo test termination_scaling -- --nocapture`.
    fn report(shape: &str, samples: &[Sample]) {
        for measured in samples {
            eprintln!(
                "termination scaling: {shape} size {} nodes {} plan {} check {}",
                measured.size, measured.nodes, measured.plan_work, measured.check_work
            );
        }
    }
}
