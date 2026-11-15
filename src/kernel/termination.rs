mod execution;
mod obligations;
pub(in crate::kernel) use completion::ProgramBodyOwner;
mod completion;
pub(crate) use completion::{
    ProgramContractBodies, ProgramContractFailure, ProgramContractGoal, ProgramContractProof,
    ProgramTerminationInputs,
};

use super::prelude::*;
use super::spec::walk::{SpecNode, Visit, WalkBudget, Walked, walk_spec};
use crate::kernel::binary_term;
use crate::kernel::{bits32_constant, constant_u32};
use std::sync::Arc;

/// Charges `units` of termination work to the ambient deterministic-work
/// counters.
///
/// The termination check has no tactic of its own, so this is measurement
/// only: it never consumes a budget and so cannot change a verdict. Every
/// unit is one step the algorithm actually takes — a statement of a body it
/// walks, a call edge it reads, a level member it settles, a planner visit,
/// or a worklist step — so `termination_scaling_tests` counts the checker
/// rather than the host clock.
pub(in crate::kernel) fn charge_termination_work(units: usize) {
    crate::instrumentation::record_deterministic_work(units);
}

/// Charges a walk that visits a sequence's statements in turn for the pair
/// nodes beyond the first that the pair tree it stands for held, so the walk
/// costs what it cost on that tree.
fn charge_seq_spine(statements: &ProgramStatementSequence) {
    charge_termination_work(statements.len() - 2);
}

/// The one library call the execution model implements itself instead of
/// looking up a function; see `c_statement_calls`.
const MODELED_REALLOC: &str = "realloc";

fn error(message: impl Into<String>) -> TerminationError {
    TerminationError {
        message: message.into(),
        function: None,
        superfluous_recursive_measure: false,
    }
}

fn int32_literal(expression: &ProgramExpression) -> Option<i64> {
    let ProgramExpression::Value(ProgramValue::Int32(value)) = expression else {
        return None;
    };
    Some(value.as_const()? as i32 as i64)
}

fn variable_minus_positive(expression: &ProgramExpression, variable: &str) -> Option<i64> {
    let ProgramExpression::Subtract(left, right) = expression else {
        return None;
    };
    if left.as_ref() != &ProgramExpression::Variable(variable.to_string()) {
        return None;
    }
    int32_literal(right).filter(|step| *step > 0)
}

fn substitute_program_expression_variables(
    expression: &ProgramExpression,
    substitutions: &BTreeMap<String, ProgramExpression>,
) -> ProgramExpression {
    use ProgramExpression::*;
    let unary = |body: &ProgramExpression| {
        Box::new(substitute_program_expression_variables(body, substitutions))
    };
    let binary = |left: &ProgramExpression, right: &ProgramExpression| {
        (
            Box::new(substitute_program_expression_variables(left, substitutions)),
            Box::new(substitute_program_expression_variables(
                right,
                substitutions,
            )),
        )
    };
    match expression {
        Value(_) | FunctionAddress(_) | StepResult { .. } => expression.clone(),
        Cast {
            expression: body,
            target_type,
            integer_mode,
            pointee_struct,
            pointee_volatile,
            pointee_constant,
            explicit_qualification,
        } => Cast {
            expression: unary(body),
            target_type: *target_type,
            integer_mode: *integer_mode,
            pointee_struct: pointee_struct.clone(),
            pointee_volatile: *pointee_volatile,
            pointee_constant: *pointee_constant,
            explicit_qualification: *explicit_qualification,
        },
        FloatClassification {
            expression: body,
            classification,
        } => FloatClassification {
            expression: unary(body),
            classification: *classification,
        },
        FloatNegate(body) => FloatNegate(unary(body)),
        EnumConstruct {
            enum_type,
            variant,
            fields,
        } => EnumConstruct {
            enum_type: *enum_type,
            variant: variant.clone(),
            fields: fields
                .iter()
                .map(|field| substitute_program_expression_variables(field, substitutions))
                .collect(),
        },
        EnumField {
            value,
            variant,
            index,
        } => EnumField {
            value: unary(value),
            variant: variant.clone(),
            index: *index,
        },
        EnumIs { value, variant } => EnumIs {
            value: unary(value),
            variant: variant.clone(),
        },
        Ternary {
            condition,
            then_branch,
            else_branch,
        } => Ternary {
            condition: unary(condition),
            then_branch: unary(then_branch),
            else_branch: unary(else_branch),
        },
        Variable(name) => substitutions
            .get(name)
            .cloned()
            .unwrap_or_else(|| expression.clone()),
        AddressOf(body) => AddressOf(unary(body)),
        CheckedObjectAddress(body) => CheckedObjectAddress(unary(body)),
        PointerOffsetBytes { pointer, bytes } => PointerOffsetBytes {
            pointer: unary(pointer),
            bytes: *bytes,
        },
        // Termination compares measure arguments structurally, as the
        // pointers they pass: a member's subobject narrowing does not change
        // which child a call passes, and the contract's child spelling has
        // none.
        Subobject { pointer, .. } => *unary(pointer),
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
        RustShiftLeft(left, right) => {
            let (left, right) = binary(left, right);
            RustShiftLeft(left, right)
        }
        ShiftRight(left, right) => {
            let (left, right) = binary(left, right);
            ShiftRight(left, right)
        }
        RustShiftRight(left, right) => {
            let (left, right) = binary(left, right);
            RustShiftRight(left, right)
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
        // Nor does the access class a member load carries for the
        // strict-aliasing check, which the contract's spelling lacks.
        TypedLoad {
            pointer,
            value_type,
            volatile,
            pointee_constant,
            access_class: _,
            source,
        } => TypedLoad {
            pointer: unary(pointer),
            value_type: *value_type,
            volatile: *volatile,
            pointee_constant: *pointee_constant,
            access_class: None,
            source: source.clone(),
        },
        Index(left, right) => {
            let (left, right) = binary(left, right);
            Index(left, right)
        }
    }
}

fn resolve_program_expression_aliases(
    expression: &ProgramExpression,
    aliases: &BTreeMap<String, ProgramExpression>,
) -> ProgramExpression {
    let mut resolved = expression.clone();
    for _ in 0..=aliases.len() {
        let next = substitute_program_expression_variables(&resolved, aliases);
        if next == resolved {
            break;
        }
        resolved = next;
    }
    resolved
}

fn instantiate_structural_guard(
    proposition: &SpecProposition,
    substitutions: &BTreeMap<String, ProgramExpression>,
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
        SpecExpression::ProgramExpression(expression) => Some(SpecExpression::ProgramExpression(
            substitute_program_expression_variables(expression, substitutions),
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
    aliases: BTreeMap<String, ProgramExpression>,
    conditions: Vec<(ProgramExpression, bool)>,
}

struct StructuralResourceMeasure {
    /// The measured resource family.
    family: String,
    arguments: Vec<ProgramExpression>,
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
    guards: Vec<ProgramExpression>,
    /// Whether the function's own `requires` already establishes a guard, so
    /// every path into the body starts inside this arm.
    guard_is_precondition: bool,
    children: Vec<Vec<ProgramExpression>>,
    /// Direct recursive children named through a `let` witness of the
    /// definition rather than a C expression of its parameters.
    witness_children: Vec<WitnessChildMeasure>,
}

struct WitnessChildMeasure {
    definition: CompositeResourceDefinition,
    /// Each child argument: a witness of `definition`, or a body expression.
    arguments: Vec<ProgramExpression>,
}

fn structural_guard_expression(proposition: &SpecProposition) -> Option<ProgramExpression> {
    let SpecProposition::Comparison {
        left,
        operator,
        right,
    } = proposition
    else {
        return None;
    };
    let expression = |expression: &SpecExpression| match expression {
        SpecExpression::Value(value) => Some(ProgramExpression::Value(value.clone())),
        SpecExpression::ProgramExpression(expression) => Some(expression.clone()),
        _ => None,
    };
    let left = Box::new(expression(left)?);
    let right = Box::new(expression(right)?);
    Some(match operator {
        ComparisonOperator::Equal => ProgramExpression::Equal(left, right),
        ComparisonOperator::NotEqual => ProgramExpression::NotEqual(left, right),
        ComparisonOperator::LessThan => ProgramExpression::LessThan(left, right),
        ComparisonOperator::LessEqual => ProgramExpression::LessEqual(left, right),
        ComparisonOperator::GreaterThan => ProgramExpression::GreaterThan(left, right),
        ComparisonOperator::GreaterEqual => ProgramExpression::GreaterEqual(left, right),
    })
}

fn branch_establishes_structural_guard(
    branch_condition: &ProgramExpression,
    branch_value: bool,
    guard: &ProgramExpression,
) -> bool {
    #[derive(Eq, PartialEq)]
    enum ConditionAtom {
        Equal(ProgramExpression, ProgramExpression),
        LessThan(ProgramExpression, ProgramExpression),
    }

    fn normalized(expression: &ProgramExpression, value: bool) -> (ConditionAtom, bool) {
        let ordered = |left: &ProgramExpression, right: &ProgramExpression| {
            if left <= right {
                (left.clone(), right.clone())
            } else {
                (right.clone(), left.clone())
            }
        };
        match expression {
            ProgramExpression::Not(body) => normalized(body, !value),
            ProgramExpression::Equal(left, right) => {
                let (left, right) = ordered(left, right);
                (ConditionAtom::Equal(left, right), value)
            }
            ProgramExpression::NotEqual(left, right) => {
                let (left, right) = ordered(left, right);
                (ConditionAtom::Equal(left, right), !value)
            }
            ProgramExpression::LessThan(left, right) => (
                ConditionAtom::LessThan(left.as_ref().clone(), right.as_ref().clone()),
                value,
            ),
            ProgramExpression::GreaterEqual(left, right) => (
                ConditionAtom::LessThan(left.as_ref().clone(), right.as_ref().clone()),
                !value,
            ),
            ProgramExpression::GreaterThan(left, right) => (
                ConditionAtom::LessThan(right.as_ref().clone(), left.as_ref().clone()),
                value,
            ),
            ProgramExpression::LessEqual(left, right) => (
                ConditionAtom::LessThan(right.as_ref().clone(), left.as_ref().clone()),
                !value,
            ),
            expression => {
                let (left, right) = ordered(
                    expression,
                    &ProgramExpression::Value(ProgramValue::Int32(MachineTerm::constant(0))),
                );
                (ConditionAtom::Equal(left, right), !value)
            }
        }
    }

    // A subobject narrowing does not change the value a comparison reads, as
    // it does not change which child a call passes.
    let structural = |expression: &ProgramExpression| {
        substitute_program_expression_variables(expression, &BTreeMap::new())
    };
    normalized(&structural(branch_condition), branch_value) == normalized(&structural(guard), true)
}

fn check_structural_recursive_call(
    function_name: &str,
    arguments: &[ProgramExpression],
    function: &ProgramFunction,
    measure: &StructuralResourceMeasure,
    callees: &BTreeMap<String, StructuralCallee>,
    path: &StructuralRecursionPath,
) -> Result<(), TerminationError> {
    // A call to a member of the recursive component passes, for that
    // member's own measured requirement, the arguments its measure is
    // written over; they must name a direct child of this function's measured
    // instance. Every member is checked this way, so each edge of the cycle
    // moves to a strictly contained child of the finite witness.
    let Some(callee) = callees.get(function_name) else {
        return Ok(());
    };
    if callee.family != measure.family {
        return Err(error(format!(
            "recursive call to `{function_name}` is ranked by the structural measure `{}`, but \
             the caller's is `{}`; the members of a structurally ranked component must measure \
             one resource family",
            callee.family, measure.family
        )));
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
    let parameter_substitutions = callee
        .parameters
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| {
            (
                parameter.clone(),
                resolve_program_expression_aliases(argument, &path.aliases),
            )
        })
        .collect::<BTreeMap<_, _>>();
    // A child is named by the pointer it passes; a member's subobject
    // narrowing does not change which child that is.
    let call_measure_arguments = callee
        .arguments
        .iter()
        .map(|argument| substitute_program_expression_variables(argument, &parameter_substitutions))
        .collect::<Vec<_>>();
    let structural = |arguments: &[ProgramExpression]| {
        arguments
            .iter()
            .map(|argument| substitute_program_expression_variables(argument, &BTreeMap::new()))
            .collect::<Vec<_>>()
    };
    let call_children = structural(&call_measure_arguments);
    if !active.iter().any(|arm| {
        arm.children
            .iter()
            .any(|child| structural(child) == call_children)
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
    function: &'a ProgramFunction,
    measure: &'a StructuralResourceMeasure,
    callees: &'a BTreeMap<String, StructuralCallee>,
}

impl TerminationWalk for StructuralMeasureWalk<'_> {
    type Path = StructuralRecursionPath;

    fn step(
        &self,
        statement: &ProgramStatement,
        paths: Vec<Self::Path>,
    ) -> Result<Vec<Self::Path>, TerminationError> {
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
            ProgramStatement::EndAutomaticLifetimes { names } => {
                Ok(names.iter().fold(paths, |paths, name| forget(name, paths)))
            }
            ProgramStatement::Skip
            | ProgramStatement::Continue
            | ProgramStatement::Goto { .. }
            | ProgramStatement::Assert { .. }
            | ProgramStatement::HeapFree { .. }
            | ProgramStatement::Store { .. }
            | ProgramStatement::TypedStore { .. }
            | ProgramStatement::CopyAggregate { .. }
            | ProgramStatement::InitializeScalarArray { .. }
            | ProgramStatement::Update { .. } => Ok(paths),
            ProgramStatement::Declare {
                name,
                initializer: None,
                ..
            }
            | ProgramStatement::DeclareAggregate { name, .. } => Ok(forget(name, paths)),
            ProgramStatement::HeapAllocate { target, .. } => Ok(forget(target, paths)),
            ProgramStatement::Declare {
                name,
                initializer: Some(expression),
                ..
            }
            | ProgramStatement::Assign {
                name, expression, ..
            } => Ok(paths
                .into_iter()
                .map(|mut path| {
                    let expression = resolve_program_expression_aliases(expression, &path.aliases);
                    path.aliases.insert(name.clone(), expression);
                    path
                })
                .collect()),
            ProgramStatement::CallConstruct {
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
                        self.callees,
                        path,
                    )?;
                }
                Ok(forget(target, paths))
            }
            ProgramStatement::Call {
                function_name,
                arguments,
                ..
            }
            | ProgramStatement::CallResult {
                function_name,
                arguments,
                ..
            } => {
                for path in &paths {
                    check_structural_recursive_call(
                        function_name,
                        arguments,
                        self.function,
                        self.measure,
                        self.callees,
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
        condition: &ProgramExpression,
        taken: bool,
        paths: Vec<Self::Path>,
    ) -> Vec<Self::Path> {
        paths
            .into_iter()
            .map(|mut path| {
                let condition = resolve_program_expression_aliases(condition, &path.aliases);
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
    statement: &ProgramStatement,
    function: &ProgramFunction,
    measure: &StructuralResourceMeasure,
    callees: &BTreeMap<String, StructuralCallee>,
    paths: Vec<StructuralRecursionPath>,
) -> Result<Vec<StructuralRecursionPath>, TerminationError> {
    Ok(walk_termination_paths(
        &StructuralMeasureWalk {
            function,
            measure,
            callees,
        },
        statement,
        paths,
    )?
    .continuing)
}

fn program_expression_mentions_variable(expression: &ProgramExpression, variable: &str) -> bool {
    // Substitution also normalizes subobject wrappers, even when no variable
    // is replaced. Such normalization cannot establish a free occurrence.
    let mut variables = BTreeSet::new();
    collect_program_expression_variables(expression, &mut variables);
    variables.contains(variable)
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
    facts: &(impl ExecutionFactSource + ?Sized),
    obligations: &[ProofObligation],
) -> Option<()> {
    for obligation in obligations {
        let proposition = obligation.proposition();
        let decided = match proposition {
            Proposition::MemoryLoadable { .. } => true,
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
    for fact in facts.fact_iter() {
        *assumptions = assumptions
            .clone()
            .assume_proposition(fact.proposition().clone());
    }
    Some(())
}

fn evaluate_structural_program_expression(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &mut PureFactContext,
    budget: &mut ExecutionBudget,
) -> Option<ProgramValue> {
    let paths = evaluate_program_expression_paths(state, expression, assumptions, budget).ok()?;
    let [path] = paths.as_slice() else {
        return None;
    };
    let ExpressionOutcome::Value(value) = &path.outcome else {
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
    function: &ProgramFunction,
    measure: &StructuralResourceMeasure,
    arm: &StructuralResourceArm,
    call_measure_arguments: &[ProgramExpression],
) -> bool {
    const PARAMETER_VARIABLE_BASE: u64 = 4_200_000_000;
    const WITNESS_VARIABLE_BASE: u64 = 4_250_000_000;
    if arm.witness_children.is_empty() {
        return false;
    }
    let mut budget = ExecutionBudget::for_new_execution();
    let entry_assumptions = PureFactContext::new()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads()
        // This scope compares symbolic child identities. The ordinary
        // contract execution separately checks the call and its accesses.
        .assume_entry_clause_extents();
    let mut parameter_state = ExecutionState::new();
    for (index, parameter) in function.parameters().iter().enumerate() {
        let variable = Variable(PARAMETER_VARIABLE_BASE + index as u64);
        let value = if parameter.program_type().is_pointer() {
            ProgramValue::typed_pointer(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(variable), 1),
                },
                parameter.program_type(),
            )
        } else {
            symbolic_call_result(parameter.program_type(), variable)
        };
        parameter_state.locals.set_typed(
            parameter.name().to_string(),
            value,
            parameter.program_type(),
        );
    }
    'children: for child in &arm.witness_children {
        let definition = &child.definition;
        if child.arguments.len() != call_measure_arguments.len() {
            continue;
        }
        let mut assumptions = entry_assumptions.clone();
        let mut body_state = ExecutionState::new();
        for (parameter, argument) in definition.parameters().iter().zip(&measure.arguments) {
            let Some(value) = evaluate_structural_program_expression(
                &parameter_state,
                argument,
                &mut assumptions,
                &mut budget,
            ) else {
                continue 'children;
            };
            if value.program_type() != parameter.program_type() {
                continue 'children;
            }
            body_state.locals.set_typed(
                parameter.name().to_string(),
                value,
                parameter.program_type(),
            );
        }
        for (index, witness) in definition.witnesses().iter().enumerate() {
            let pointer = Pointer::symbolic(Variable(WITNESS_VARIABLE_BASE + index as u64));
            body_state.locals.set_typed(
                witness.name().to_string(),
                ProgramValue::typed_pointer(pointer, witness.program_type()),
                witness.program_type(),
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
            let Some(expected) = evaluate_structural_program_expression(
                &body_state,
                expected,
                &mut assumptions,
                &mut budget,
            ) else {
                continue 'children;
            };
            let Some(actual) = evaluate_structural_program_expression(
                &parameter_state,
                actual,
                &mut assumptions,
                &mut budget,
            ) else {
                continue 'children;
            };
            let (ProgramValue::Pointer(expected), ProgramValue::Pointer(actual)) =
                (expected, actual)
            else {
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
    function: &ProgramFunction,
    requirement_index: usize,
) -> Result<StructuralResourceMeasure, TerminationError> {
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
    let mentions_witness = |expression: &ProgramExpression| {
        definition
            .witnesses()
            .iter()
            .any(|witness| program_expression_mentions_variable(expression, witness.name()))
    };
    let mentions_binding = |expression: &ProgramExpression, bound: &BTreeSet<String>| {
        bound
            .iter()
            .any(|binding| program_expression_mentions_variable(expression, binding))
    };
    let structural_children = |contained: &[ResourceSpec],
                               bound: &BTreeSet<String>|
     -> (Vec<Vec<ProgramExpression>>, Vec<WitnessChildMeasure>) {
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
                        .map(|argument| {
                            substitute_program_expression_variables(argument, &substitutions)
                        })
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
                if child.arguments.iter().any(|argument| match argument {
                    SpecExpression::ProgramExpression(argument) => {
                        mentions_binding(argument, &bound) || mentions_witness(argument)
                    }
                    _ => true,
                }) {
                    continue;
                }
                children.push(
                    child
                        .arguments
                        .iter()
                        .filter_map(|argument| match argument {
                            SpecExpression::ProgramExpression(argument) => Some(
                                substitute_program_expression_variables(argument, &substitutions),
                            ),
                            _ => None,
                        })
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
        family: name.to_string(),
        arguments: arguments.to_vec(),
        arms,
    })
}

/// What a structural measure walk needs to know about one member of the
/// recursive component it may call: the parameters the member's measure is
/// written over, and the measured family and arguments.
struct StructuralCallee {
    parameters: Vec<String>,
    family: String,
    arguments: Vec<ProgramExpression>,
}

/// The measured family and arguments of `function`'s structural measure,
/// without the arm analysis [`structural_resource_children`] performs.
fn structural_callee(
    function: &ProgramFunction,
    requirement_index: usize,
) -> Result<StructuralCallee, TerminationError> {
    let invalid = || {
        error(format!(
            "structural resource measure index is invalid for `{}`",
            function.name()
        ))
    };
    let resource = function
        .resource_requires()
        .get(requirement_index)
        .ok_or_else(invalid)?;
    let term = resource
        .term()
        .instance_resource()
        .unwrap_or_else(|| resource.term());
    let (Some(family), Some(arguments)) = (term.declared_name(), term.declared_arguments()) else {
        return Err(invalid());
    };
    Ok(StructuralCallee {
        parameters: function
            .parameters()
            .iter()
            .map(|parameter| parameter.name().to_string())
            .collect(),
        family: family.to_string(),
        arguments: arguments.to_vec(),
    })
}

fn refined_lower_bound(
    condition: &ProgramExpression,
    variable: &str,
    branch: bool,
    current: i64,
) -> i64 {
    use ProgramExpression::*;
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
fn expression_address_taken_locals(expression: &ProgramExpression, names: &mut BTreeSet<String>) {
    use ProgramExpression::*;
    let mut inner = |body: &ProgramExpression| expression_address_taken_locals(body, names);
    match expression {
        Value(_) | Variable(_) | FunctionAddress(_) | StepResult { .. } => {}
        Cast { expression, .. } => inner(expression),
        FloatNegate(expression)
        | FloatClassification { expression, .. }
        | EnumField {
            value: expression, ..
        }
        | EnumIs {
            value: expression, ..
        } => inner(expression),
        EnumConstruct { fields, .. } => {
            for field in fields {
                inner(field);
            }
        }
        Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            inner(condition);
            inner(then_branch);
            inner(else_branch);
        }
        AddressOf(body) | CheckedObjectAddress(body) => {
            if let Variable(target) = body.as_ref() {
                names.insert(target.clone());
            } else {
                inner(body);
            }
        }
        PointerOffsetBytes { pointer, .. }
        | Subobject { pointer, .. }
        | TypedLoad { pointer, .. } => inner(pointer),
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
        | RustShiftLeft(left, right)
        | RustShiftRight(left, right)
        | ShiftRight(left, right)
        | BitwiseAnd(left, right)
        | BitwiseOr(left, right)
        | BitwiseXor(left, right)
        | Index(left, right) => {
            inner(left);
            inner(right);
        }
    }
}

fn collect_program_expression_variables(
    expression: &ProgramExpression,
    names: &mut BTreeSet<String>,
) {
    use ProgramExpression::*;
    match expression {
        Variable(name) => {
            names.insert(name.clone());
        }
        StepResult { .. } => {}
        Cast { expression, .. }
        | FloatNegate(expression)
        | FloatClassification { expression, .. }
        | EnumField {
            value: expression, ..
        }
        | EnumIs {
            value: expression, ..
        }
        | AddressOf(expression)
        | CheckedObjectAddress(expression)
        | PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | Subobject {
            pointer: expression,
            ..
        }
        | Not(expression)
        | BitwiseNot(expression)
        | Load(expression) => collect_program_expression_variables(expression, names),
        EnumConstruct { fields, .. } => {
            for field in fields {
                collect_program_expression_variables(field, names);
            }
        }
        Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_program_expression_variables(condition, names);
            collect_program_expression_variables(then_branch, names);
            collect_program_expression_variables(else_branch, names);
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
        | RustShiftLeft(left, right)
        | RustShiftRight(left, right)
        | ShiftRight(left, right)
        | BitwiseAnd(left, right)
        | BitwiseOr(left, right)
        | BitwiseXor(left, right)
        | Index(left, right) => {
            collect_program_expression_variables(left, names);
            collect_program_expression_variables(right, names);
        }
        TypedLoad { pointer, .. } => collect_program_expression_variables(pointer, names),
        Value(_) | FunctionAddress(_) => {}
    }
}

/// The locals whose address some expression in `statement` takes. A local's
/// cell can be written through a pointer only if its address was taken
/// somewhere in the function, so this is the complete syntactic condition
/// for "a store or a callee might change this local without assigning it by
/// name". One walk of the function answers every local the checks below ask
/// about.
pub(super) fn address_taken_locals(statement: &ProgramStatement) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_address_taken_locals(statement, &mut names);
    names
}

fn collect_address_taken_locals(statement: &ProgramStatement, names: &mut BTreeSet<String>) {
    charge_termination_work(1);
    let mut escapes =
        |expression: &ProgramExpression| expression_address_taken_locals(expression, names);
    match statement {
        ProgramStatement::Skip
        | ProgramStatement::EndScalarReference(_)
        | ProgramStatement::ScalarReferenceScope(_)
        | ProgramStatement::EndAutomaticLifetimes { .. }
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::Declare {
            initializer: None, ..
        }
        | ProgramStatement::DeclareAggregate { .. } => {}
        ProgramStatement::ForStep { step, .. } => collect_address_taken_locals(step, names),
        ProgramStatement::Declare {
            initializer: Some(expression),
            ..
        }
        | ProgramStatement::Assign { expression, .. }
        | ProgramStatement::Return(expression)
        | ProgramStatement::Throw(expression) => escapes(expression),
        ProgramStatement::CallConstruct { arguments, .. }
        | ProgramStatement::Call { arguments, .. }
        | ProgramStatement::CallResult { arguments, .. } => arguments.iter().for_each(escapes),
        ProgramStatement::HeapAllocate { bytes, .. } => escapes(bytes),
        ProgramStatement::HeapFree { pointer } => escapes(pointer),
        ProgramStatement::Assert { condition, .. }
        | ProgramStatement::LoopTest { condition }
        | ProgramStatement::StepValue {
            expression: condition,
            ..
        } => escapes(condition),
        ProgramStatement::Store { pointer, value }
        | ProgramStatement::TypedStore { pointer, value, .. } => {
            escapes(pointer);
            escapes(value);
        }
        ProgramStatement::CopyAggregate { target, source, .. }
        | ProgramStatement::InitializeScalarArray { target, source, .. } => {
            escapes(target);
            escapes(source);
        }
        ProgramStatement::Update {
            target, operand, ..
        } => {
            escapes(target);
            escapes(operand);
        }
        ProgramStatement::Seq(statements) => {
            charge_seq_spine(statements);
            for statement in statements.iter() {
                collect_address_taken_locals(statement, names);
            }
        }
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            collect_address_taken_locals(try_body, names);
            collect_address_taken_locals(handler, names);
        }
        ProgramStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            escapes(condition);
            collect_address_taken_locals(then_branch, names);
            collect_address_taken_locals(else_branch, names);
        }
        ProgramStatement::While {
            condition, body, ..
        } => {
            escapes(condition);
            collect_address_taken_locals(body, names);
        }
        ProgramStatement::Switch { expression, cases } => {
            escapes(expression);
            for case in cases {
                collect_address_taken_locals(&case.body, names);
            }
        }
    }
}

/// The ranking checkers below are syntactic over assignments by name, so a
/// measure whose address escapes could be reset through a pointer, directly
/// or by a callee, without any ranked update. Such measures are rejected.
fn reject_address_escaped_measure(
    function_name: &str,
    measure: &str,
    addressed: &BTreeSet<String>,
) -> Result<(), TerminationError> {
    if addressed.contains(measure) {
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
pub(super) fn program_reject_address_escaped_loop_measures(
    function_name: &str,
    measures: &[RankingComponent],
    addressed: &BTreeSet<String>,
) -> Result<(), String> {
    for measure in measures {
        reject_address_escaped_ranking_component(function_name, measure, addressed)
            .map_err(|error| error.message)?;
    }
    Ok(())
}

fn reject_address_escaped_expression_measure(
    function_name: &str,
    measure: &ProgramExpression,
    addressed: &BTreeSet<String>,
) -> Result<(), TerminationError> {
    let mut variables = BTreeSet::new();
    collect_program_expression_variables(measure, &mut variables);
    for variable in variables {
        reject_address_escaped_measure(function_name, &variable, addressed)?;
    }
    Ok(())
}

/// What one pure `decreases` component reads, collected from its lowered
/// expression: the C locals it names, whether it reads C memory, and whether
/// it reads the algebraic model of a resource binder.
#[derive(Default)]
struct MeasureReads {
    variables: BTreeSet<String>,
    memory: bool,
    model: bool,
}

impl MeasureReads {
    /// The first C read, by spelling, for a refusal that names it.
    fn first_program_read(&self) -> Option<String> {
        self.variables
            .iter()
            .next()
            .map(|name| format!("the C variable `{name}`"))
            .or_else(|| self.memory.then(|| "C memory".to_string()))
    }
}

/// The same check for one certified `decreases` component.
///
/// A measure names a local's *value*, so a local whose address escapes is not
/// one the measure can read; that is what the C form already refuses. A pure
/// component reaches the same locals through its lowered C fragments, so the
/// names it reads are collected from the lowered expression. A lowered form
/// this collection does not cover is refused outright rather than passed
/// unchecked: the escape check is the kernel's, not the surface's.
///
/// A component that reads a resource binder's algebraic model is a model
/// measure: a function of the loop binders' models alone. It may not also
/// read C state. Its two readings are the head binders' models and the
/// rebound binders' models, and nothing else may move between them.
fn reject_address_escaped_ranking_component(
    function_name: &str,
    component: &RankingComponent,
    addressed: &BTreeSet<String>,
) -> Result<(), TerminationError> {
    let (source, collected) = match component {
        RankingComponent::ProgramExpression(expression) => {
            return reject_address_escaped_expression_measure(function_name, expression, addressed);
        }
        RankingComponent::Pure { source, expression } => {
            let mut reads = MeasureReads::default();
            (
                source,
                collect_spec_program_variables(SpecNode::Expression(expression), &mut reads)
                    .map(|()| reads),
            )
        }
        RankingComponent::PureInteger { source, expression } => {
            let mut reads = MeasureReads::default();
            (
                source,
                collect_spec_program_variables(SpecNode::Integer(expression), &mut reads)
                    .map(|()| reads),
            )
        }
    };
    let reads = collected.map_err(|form| {
        error(format!(
            "the `decreases` component `{source}` in `{function_name}` contains {form}, which a \
             termination measure cannot contain; write the measure as arithmetic over C values, \
             resource fields and models, and pure function applications"
        ))
    })?;
    if reads.model
        && let Some(read) = reads.first_program_read()
    {
        return Err(error(format!(
            "the `decreases` component `{source}` in `{function_name}` reads a resource binder's \
             model and also {read}; a measure over a model may read only the loop's resource \
             binders' models and fields, constants, and pure functions of them"
        )));
    }
    for variable in reads.variables {
        reject_address_escaped_measure(function_name, &variable, addressed)?;
    }
    Ok(())
}

/// The form a measure collection does not read, named for the refusal.
type UncollectedForm = &'static str;

/// Collects the C locals one lowered specification subtree reads, or names
/// the first form it contains that this collection does not cover.
///
/// Every machine, Integer and algebraic form is listed, so a new form is
/// refused until it is reviewed here. A kernel `IntegerTerm` or a C value
/// names no source local: a local a measure reads reaches the Integer carrier
/// through `FromMachine`, or as a pure application's machine argument, and
/// both are walked. A resource field reads the binder's instance, not a C
/// local; in the algebraic carrier it is a binder's model, which is what marks
/// the component a model measure. An algebraic variable or a match binding is
/// a pure value, not a C local.
///
/// Work is linear in the expression, which is the declared component; nothing
/// ambient is scanned.
fn collect_spec_program_variables(
    root: SpecNode<'_>,
    reads: &mut MeasureReads,
) -> Result<(), UncollectedForm> {
    let walked = walk_spec(root, WalkBudget::Unmetered, |node| {
        match node {
            SpecNode::Expression(expression) => {
                charge_termination_work(1);
                match expression {
                    SpecExpression::ProgramExpression(expression) => {
                        collect_program_expression_variables(expression, &mut reads.variables);
                    }
                    SpecExpression::MemoryLoad { .. } => reads.memory = true,
                    SpecExpression::Value(_)
                    | SpecExpression::ResourceField { .. }
                    | crate::kernel::binary_spec_expression!(_, _)
                    | SpecExpression::Subobject { .. }
                    | SpecExpression::PointerOffset { .. }
                    | SpecExpression::BitwiseNot(_)
                    | SpecExpression::NarrowArithmetic(_, _)
                    | SpecExpression::Cast(_, _)
                    | SpecExpression::PointerCoercion(_, _)
                    | SpecExpression::PureFunctionApplication { .. }
                    | SpecExpression::IntegerToMachine { .. }
                    | SpecExpression::AlgebraicMatch { .. } => {}
                    SpecExpression::CountedResourceCount { .. } => {
                        return Visit::Stop("a counted-resource count");
                    }
                    SpecExpression::If { .. } => {
                        return Visit::Stop("a conditional `if` expression");
                    }
                    SpecExpression::Requires { .. } => {
                        return Visit::Stop("a subslice's bounds requirement");
                    }
                    SpecExpression::RangeFold { .. } => return Visit::Stop("a range fold"),
                    SpecExpression::Let { .. } => return Visit::Stop("a `let` expression"),
                    SpecExpression::LoopEntryState(_) => {
                        return Visit::Stop("a loop-entry state");
                    }
                    SpecExpression::AggregateFieldValue { .. } => {
                        return Visit::Stop("a by-value aggregate field");
                    }
                }
            }
            SpecNode::Integer(integer) => {
                charge_termination_work(1);
                match integer {
                    SpecIntegerExpression::Term(_)
                    | SpecIntegerExpression::ResourceField(_)
                    | SpecIntegerExpression::FromMachine(_)
                    | SpecIntegerExpression::Negate(_)
                    | crate::kernel::binary_spec_integer_expression!(_, _)
                    | SpecIntegerExpression::PureFunctionApplication { .. }
                    | SpecIntegerExpression::AlgebraicMatch { .. } => {}
                    SpecIntegerExpression::If { .. } => {
                        return Visit::Stop("a conditional `if` expression");
                    }
                    SpecIntegerExpression::RangeFold { .. } => return Visit::Stop("a range fold"),
                }
            }
            SpecNode::Algebraic(algebraic) => {
                charge_termination_work(1);
                match &algebraic.node {
                    SpecAlgebraicExpressionNode::ResourceField(_) => reads.model = true,
                    SpecAlgebraicExpressionNode::Variable(_)
                    | SpecAlgebraicExpressionNode::Binding(_)
                    | SpecAlgebraicExpressionNode::Constructor { .. }
                    | SpecAlgebraicExpressionNode::Match { .. }
                    | SpecAlgebraicExpressionNode::PureFunctionApplication { .. }
                    | SpecAlgebraicExpressionNode::ProgramValue(_) => {}
                    SpecAlgebraicExpressionNode::If { .. } => {
                        return Visit::Stop("a conditional `if` expression");
                    }
                }
            }
            SpecNode::Argument(SpecPureFunctionArgument::ArrayRef { .. }) => reads.memory = true,
            // Only a refused `if` reaches a proposition, and through it a
            // sequence or a resource.
            SpecNode::Argument(_)
            | SpecNode::AlgebraicValue(_)
            | SpecNode::Proposition(_)
            | SpecNode::PredicateArgument(_)
            | SpecNode::Sequence(_)
            | SpecNode::Resource(_) => {}
        }
        Visit::Descend
    });
    match walked {
        Walked::Stopped(form) => Err(form),
        Walked::Completed | Walked::OutOfTime => Ok(()),
    }
}

fn statement_calls(statement: &ProgramStatement, calls: &mut BTreeSet<String>) {
    statement_calls_visiting(statement, calls, &mut |_| true);
}

/// The functions `function`'s body calls by name: the call graph of a body a
/// typed frontend lowered itself, which has no C syntax to read calls from.
pub fn program_function_callees(function: &ProgramFunction) -> BTreeSet<String> {
    let mut calls = BTreeSet::new();
    statement_calls(&function.source_body, &mut calls);
    calls
}

/// Identity memoization visits a shared summary body once even when distinct
/// checked theorems apply it at different states. The evidence keeps every
/// node alive for the traversal; no deep structural key is constructed.
pub(in crate::kernel) fn checked_statement_calls(
    statement: &ProgramStatement,
    seen: &mut std::collections::HashSet<usize>,
    calls: &mut BTreeSet<String>,
) {
    statement_calls_visiting(statement, calls, &mut |node| {
        seen.insert(node as *const ProgramStatement as usize)
    });
}

fn statement_calls_visiting(
    statement: &ProgramStatement,
    calls: &mut BTreeSet<String>,
    visit: &mut impl FnMut(&ProgramStatement) -> bool,
) {
    charge_termination_work(1);
    if !visit(statement) {
        return;
    }
    match statement {
        // A call through a function pointer reaches whatever the pointer
        // holds, which no function name says.
        ProgramStatement::Call {
            function_name,
            callee: Some(_),
            ..
        }
        | ProgramStatement::CallResult {
            function_name,
            callee: Some(_),
            ..
        } => {
            calls.insert(format!("{function_name}#indirect"));
        }
        ProgramStatement::CallConstruct { function_name, .. }
        | ProgramStatement::Call { function_name, .. }
        | ProgramStatement::CallResult { function_name, .. } => {
            calls.insert(function_name.clone());
        }
        ProgramStatement::Seq(statements) => {
            charge_seq_spine(statements);
            for statement in statements.iter() {
                statement_calls_visiting(statement, calls, visit);
            }
        }
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            statement_calls_visiting(try_body, calls, visit);
            statement_calls_visiting(handler, calls, visit);
        }
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            statement_calls_visiting(then_branch, calls, visit);
            statement_calls_visiting(else_branch, calls, visit);
        }
        ProgramStatement::While { body, .. } => statement_calls_visiting(body, calls, visit),
        ProgramStatement::Switch {
            expression: _,
            cases,
        } => {
            for case in cases {
                statement_calls_visiting(&case.body, calls, visit);
            }
        }
        ProgramStatement::ForStep { step, .. } => statement_calls_visiting(step, calls, visit),
        ProgramStatement::Skip
        | ProgramStatement::EndScalarReference(_)
        | ProgramStatement::ScalarReferenceScope(_)
        | ProgramStatement::EndAutomaticLifetimes { .. }
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::Declare { .. }
        | ProgramStatement::DeclareAggregate { .. }
        | ProgramStatement::Assign { .. }
        | ProgramStatement::HeapAllocate { .. }
        | ProgramStatement::HeapFree { .. }
        | ProgramStatement::Assert { .. }
        | ProgramStatement::StepValue { .. }
        | ProgramStatement::LoopTest { .. }
        | ProgramStatement::Throw(_)
        | ProgramStatement::Return(_)
        | ProgramStatement::Store { .. }
        | ProgramStatement::TypedStore { .. }
        | ProgramStatement::CopyAggregate { .. }
        | ProgramStatement::InitializeScalarArray { .. }
        | ProgramStatement::Update { .. } => {}
    }
}

/// Collects the names this body declares, so a call through one of them is
/// not mistaken for a call to a like-named function.
fn statement_declared_variables(statement: &ProgramStatement, names: &mut BTreeSet<String>) {
    charge_termination_work(1);
    match statement {
        ProgramStatement::Declare { name, .. }
        | ProgramStatement::DeclareAggregate { name, .. }
        | ProgramStatement::CallConstruct { target: name, .. }
        | ProgramStatement::HeapAllocate { target: name, .. } => {
            names.insert(name.clone());
        }
        ProgramStatement::Seq(statements) => {
            charge_seq_spine(statements);
            for statement in statements.iter() {
                statement_declared_variables(statement, names);
            }
        }
        ProgramStatement::TryCatchInt32 {
            try_body,
            binding,
            handler,
            ..
        } => {
            statement_declared_variables(try_body, names);
            names.insert(binding.clone());
            statement_declared_variables(handler, names);
        }
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            statement_declared_variables(then_branch, names);
            statement_declared_variables(else_branch, names);
        }
        ProgramStatement::While { body, .. } => statement_declared_variables(body, names),
        ProgramStatement::Switch { cases, .. } => {
            for case in cases {
                statement_declared_variables(&case.body, names);
            }
        }
        ProgramStatement::ForStep { step, .. } => statement_declared_variables(step, names),
        ProgramStatement::Skip
        | ProgramStatement::EndScalarReference(_)
        | ProgramStatement::ScalarReferenceScope(_)
        | ProgramStatement::EndAutomaticLifetimes { .. }
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::Assign { .. }
        | ProgramStatement::Update { .. }
        | ProgramStatement::Call { .. }
        | ProgramStatement::CallResult { .. }
        | ProgramStatement::HeapFree { .. }
        | ProgramStatement::Assert { .. }
        | ProgramStatement::StepValue { .. }
        | ProgramStatement::LoopTest { .. }
        | ProgramStatement::Throw(_)
        | ProgramStatement::Return(_)
        | ProgramStatement::Store { .. }
        | ProgramStatement::TypedStore { .. }
        | ProgramStatement::CopyAggregate { .. }
        | ProgramStatement::InitializeScalarArray { .. } => {}
    }
}

/// The names `function` binds as objects: its parameters and everything its
/// body declares.
fn function_object_names(function: &ProgramFunction) -> BTreeSet<String> {
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
        statement: &ProgramStatement,
        paths: Vec<Self::Path>,
    ) -> Result<Vec<Self::Path>, TerminationError>;

    /// The paths entering a branch arm or a loop body, refined by the
    /// condition that selects it.
    fn refine(
        &self,
        condition: &ProgramExpression,
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
    statement: &ProgramStatement,
    paths: Vec<W::Path>,
) -> Result<WalkPaths<W::Path>, TerminationError> {
    let descend = |statement: &ProgramStatement, paths: Vec<W::Path>| {
        walk_termination_paths(walk, statement, paths)
    };
    match statement {
        ProgramStatement::ForStep { step, .. } => descend(step, paths),
        ProgramStatement::Return(_) | ProgramStatement::Throw(_) => Ok(WalkPaths::none()),
        // A `break` leaves the innermost `switch` or loop and resumes after
        // it, carrying what it holds here. It does not reach the next
        // statement in this body, which is what `continuing` is empty for.
        ProgramStatement::Break => Ok(WalkPaths {
            continuing: Vec::new(),
            broken: paths,
        }),
        ProgramStatement::Seq(statements) => {
            let first = descend(statements.first(), paths)?;
            let mut second = descend(&statements.rest(), first.continuing)?;
            second.broken.extend(first.broken);
            Ok(second)
        }
        ProgramStatement::TryCatchInt32 {
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
        ProgramStatement::If {
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
        ProgramStatement::While {
            condition, body, ..
        } => {
            // A `break` in the body lands where the loop's own exit lands,
            // carrying what the incoming paths already carry, so it is
            // covered by the incoming paths this returns.
            descend(body, walk.refine(condition, true, paths.clone()))?;
            Ok(WalkPaths::continuing(paths))
        }
        ProgramStatement::Switch { cases, .. } => {
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
            if !cases.iter().any(|case| case.value.is_none()) {
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
        arguments: &[ProgramExpression],
        lower_bounds: &[i64],
    ) -> Result<(), TerminationError> {
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
        statement: &ProgramStatement,
        lower_bounds: Vec<i64>,
    ) -> Result<Vec<i64>, TerminationError> {
        let measure = self.measure;
        match statement {
            ProgramStatement::EndAutomaticLifetimes { names } => {
                if names.iter().any(|name| name == measure) {
                    return Err(error(format!(
                        "termination measure `{measure}` leaves its lifetime"
                    )));
                }
                Ok(lower_bounds)
            }
            ProgramStatement::Skip
            | ProgramStatement::Continue
            | ProgramStatement::Goto { .. }
            | ProgramStatement::Declare { .. }
            | ProgramStatement::DeclareAggregate { .. }
            | ProgramStatement::Assert { .. }
            | ProgramStatement::HeapFree { .. }
            | ProgramStatement::Store { .. }
            | ProgramStatement::TypedStore { .. }
            | ProgramStatement::CopyAggregate { .. }
            | ProgramStatement::InitializeScalarArray { .. } => Ok(lower_bounds),
            ProgramStatement::Assign { name, .. } if name == measure => Err(error(format!(
                "termination measure `{measure}` is reassigned; this first implementation requires an unchanged function parameter"
            ))),
            ProgramStatement::Assign { .. } => Ok(lower_bounds),
            ProgramStatement::Update {
                target: ProgramExpression::Variable(name),
                ..
            } if name == measure => Err(error(format!(
                "termination measure `{measure}` is updated; this first implementation requires an unchanged function parameter"
            ))),
            ProgramStatement::Update { .. } => Ok(lower_bounds),
            ProgramStatement::HeapAllocate { target, .. } if target == measure => {
                Err(error(format!(
                    "recursive termination measure `{measure}` is overwritten by an allocation result"
                )))
            }
            ProgramStatement::HeapAllocate { .. } => Ok(lower_bounds),
            ProgramStatement::CallConstruct {
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
            ProgramStatement::Call {
                function_name,
                arguments,
                ..
            }
            | ProgramStatement::CallResult {
                function_name,
                arguments,
                ..
            } => {
                self.check_recursive_call(function_name, arguments, &lower_bounds)?;
                Ok(lower_bounds)
            }
            statement => unreachable!("control flow is the skeleton's: {statement:?}"),
        }
    }

    fn refine(
        &self,
        condition: &ProgramExpression,
        taken: bool,
        lower_bounds: Vec<i64>,
    ) -> Vec<i64> {
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
    statement: &ProgramStatement,
    measure: &str,
    component: &BTreeSet<String>,
    parameter_indices: &BTreeMap<String, usize>,
    lower_bounds: Vec<i64>,
) -> Result<Vec<i64>, TerminationError> {
    let walk = Int32MeasureWalk {
        measure,
        component,
        parameter_indices,
    };
    Ok(walk_termination_paths(&walk, statement, lower_bounds)?.continuing)
}

/// The identity spelling of a measure, which [`loop_measures_name_same_declaration`]
/// compares a pure component's written source against and which a pure
/// component's source is built from. It must keep telling different measures
/// apart, so a form it has no spelling for stays structural. Diagnostics use
/// [`termination_measure_display`] instead.
fn termination_measure_key(measure: &ProgramExpression) -> String {
    use ProgramExpression::*;
    let binary = |left: &ProgramExpression, right: &ProgramExpression, operator: &str| {
        format!(
            "{} {operator} {}",
            termination_measure_key(left),
            termination_measure_key(right)
        )
    };
    match measure {
        Variable(name) => name.clone(),
        Value(ProgramValue::Int32(term)) | Value(ProgramValue::UInt8(term)) => {
            match term.as_const() {
                Some(value) => format!("{}", value as i32),
                None => format!("{measure:?}"),
            }
        }
        Add(left, right) => binary(left, right, "+"),
        Subtract(left, right) => binary(left, right, "-"),
        Multiply(left, right) => binary(left, right, "*"),
        Divide(left, right) => binary(left, right, "/"),
        Remainder(left, right) => binary(left, right, "%"),
        // The kernel expression no longer carries a field's name, so a read is
        // shown as the dereference it is, with its byte offset.
        TypedLoad { pointer, .. } | Load(pointer) => {
            format!("*({})", termination_measure_key(pointer))
        }
        PointerOffsetBytes { pointer, bytes } => {
            format!("{} + {bytes} bytes", termination_measure_key(pointer))
        }
        Subobject { pointer, .. } => termination_measure_key(pointer),
        Index(base, index) => format!(
            "{}[{}]",
            termination_measure_key(base),
            termination_measure_key(index)
        ),
        Cast { expression, .. } => termination_measure_key(expression),
        _ => format!("{measure:?}"),
    }
}

/// A measure as the diagnostics show it. A part with no source spelling —
/// a value only the lowering has a name for — reads `…`, never as a kernel
/// term dump. This is presentation only; declarations are identified by
/// [`termination_measure_key`].
fn termination_measure_display(measure: &ProgramExpression) -> String {
    use ProgramExpression::*;
    let binary = |left: &ProgramExpression, right: &ProgramExpression, operator: &str| {
        format!(
            "{} {operator} {}",
            termination_measure_display(left),
            termination_measure_display(right)
        )
    };
    let unary = |operand: &ProgramExpression, operator: &str| {
        format!("{operator}({})", termination_measure_display(operand))
    };
    match measure {
        Variable(name) => name.clone(),
        Value(ProgramValue::Int32(term)) | Value(ProgramValue::UInt8(term)) => {
            match term.as_const() {
                Some(value) => format!("{}", value as i32),
                None => "…".to_string(),
            }
        }
        Add(left, right) => binary(left, right, "+"),
        Subtract(left, right) => binary(left, right, "-"),
        Multiply(left, right) => binary(left, right, "*"),
        Divide(left, right) => binary(left, right, "/"),
        Remainder(left, right) => binary(left, right, "%"),
        ShiftLeft(left, right) => binary(left, right, "<<"),
        RustShiftLeft(left, right) => binary(left, right, "<<"),
        ShiftRight(left, right) => binary(left, right, ">>"),
        RustShiftRight(left, right) => binary(left, right, ">>"),
        BitwiseAnd(left, right) => binary(left, right, "&"),
        BitwiseOr(left, right) => binary(left, right, "|"),
        BitwiseXor(left, right) => binary(left, right, "^"),
        LessThan(left, right) => binary(left, right, "<"),
        LessEqual(left, right) => binary(left, right, "<="),
        GreaterThan(left, right) => binary(left, right, ">"),
        GreaterEqual(left, right) => binary(left, right, ">="),
        Equal(left, right) => binary(left, right, "=="),
        NotEqual(left, right) => binary(left, right, "!="),
        And(left, right) => binary(left, right, "&&"),
        Or(left, right) => binary(left, right, "||"),
        BitwiseNot(operand) => unary(operand, "~"),
        Not(operand) => unary(operand, "!"),
        AddressOf(operand) => unary(operand, "&"),
        CheckedObjectAddress(operand) => format!(
            "checked object address of {}",
            termination_measure_display(operand)
        ),
        FunctionAddress(name) => format!("&{name}"),
        // The kernel expression no longer carries a field's name, so a read is
        // shown as the dereference it is, with its byte offset.
        TypedLoad { pointer, .. } | Load(pointer) => {
            format!("*({})", termination_measure_display(pointer))
        }
        PointerOffsetBytes { pointer, bytes } => {
            format!("{} + {bytes} bytes", termination_measure_display(pointer))
        }
        Subobject { pointer, .. } => termination_measure_display(pointer),
        Index(base, index) => format!(
            "{}[{}]",
            termination_measure_display(base),
            termination_measure_display(index)
        ),
        Cast { expression, .. } => termination_measure_display(expression),
        Ternary { .. }
        | FloatNegate(_)
        | FloatClassification { .. }
        | EnumConstruct { .. }
        | EnumField { .. }
        | EnumIs { .. }
        | StepResult { .. }
        | Value(_) => "…".to_string(),
    }
}

/// What evaluating a measure's memory reads at one state left behind: the
/// facts the evaluator published and the obligations it could not discharge
/// itself, which are the reads' loadability.
#[derive(Default)]
pub(super) struct RankingMeasureReads {
    pub(super) facts: crate::kernel::ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
}

/// Where a measure's memory reads are evaluated. A measure over locals alone
/// needs none of it and is read from the state by itself.
pub(super) struct RankingMeasureReader<'a> {
    pub(super) assumptions: &'a PureFactContext,
    pub(super) budget: &'a mut ExecutionBudget,
    pub(super) reads: RankingMeasureReads,
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
pub(super) fn ranking_measure_term(
    component: &RankingComponent,
    state: &ExecutionState,
    reader: &mut RankingMeasureReader<'_>,
) -> Result<RankingMeasureValue, String> {
    match component {
        // The declared measure is read as one affine form over the state's
        // own values. Folding it keeps `n - (i + 1)` from carrying an
        // intermediate `i + 1` whose definedness would need a bound the
        // measure never claims, and makes the member a stable function of the
        // declaration rather than of the assignment order that produced the
        // state.
        RankingComponent::ProgramExpression(expression) => {
            ranking_measure_term_unfolded(expression, state, reader)
                .map(RankingMachineTerm::folded_measure_value)
        }
        RankingComponent::Pure { expression, .. } => {
            pure_ranking_measure_term(expression, state, reader)
        }
        RankingComponent::PureInteger { expression, .. } => {
            pure_integer_ranking_measure_term(expression, state, reader)
                .map(RankingMeasureValue::Integer)
        }
    }
}

/// `0 <= m` for one reading of a component, in that component's carrier.
///
/// An unsigned reading is a natural number by construction, so its member is
/// the constant `true`: it keeps the bundle's one-member-per-component shape
/// without asking a proof for anything. The Integer image `to_integer(n)` of
/// a `Nat` is the same case: the checked conversion law
/// `nat::to_integer_nonnegative` states exactly this member.
pub(super) fn ranking_nonnegative_proposition(value: &RankingMeasureValue) -> Proposition {
    Proposition::ConditionIs(
        match value {
            RankingMeasureValue::Machine(term) => {
                ConditionTerm::signed_less_equal(MachineTerm::constant(0), term.clone())
            }
            // A signed 64-bit reading owes its lower bound as an int32 does.
            RankingMeasureValue::Signed64(term) => {
                ConditionTerm::int64_signed_less_equal(MachineTerm::int64_constant(0), term.clone())
            }
            RankingMeasureValue::Unsigned32(_) | RankingMeasureValue::Unsigned64(_) => {
                ConditionTerm::Constant(true)
            }
            RankingMeasureValue::Integer(term) if crate::kernel::is_nat_integer_image(term) => {
                ConditionTerm::Constant(true)
            }
            RankingMeasureValue::Integer(term) => {
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
    post: &RankingMeasureValue,
    pre: &RankingMeasureValue,
    component: &RankingComponent,
) -> Result<Proposition, String> {
    Ok(Proposition::ConditionIs(
        match (post, pre) {
            (RankingMeasureValue::Machine(post), RankingMeasureValue::Machine(pre)) => {
                ConditionTerm::signed_less_than(post.clone(), pre.clone())
            }
            // Unsigned descent compares the two wrapped values C computes.
            // Strict `<` on the naturals below 2^32 (or 2^64) is well founded,
            // so a measure that wraps is still ranked soundly: a back edge
            // whose wrapped value grows simply fails this member.
            (RankingMeasureValue::Unsigned32(post), RankingMeasureValue::Unsigned32(pre)) => {
                ConditionTerm::unsigned_less_than(post.clone(), pre.clone())
            }
            (RankingMeasureValue::Unsigned64(post), RankingMeasureValue::Unsigned64(pre)) => {
                ConditionTerm::uint64_less_than(post.clone(), pre.clone())
            }
            // Signed descent below a value that is at least zero: strict `<`
            // on the nonnegative int64 values is well founded, and the
            // bundle's `0 <= m` member keeps each reading among them.
            (RankingMeasureValue::Signed64(post), RankingMeasureValue::Signed64(pre)) => {
                ConditionTerm::int64_signed_less_than(post.clone(), pre.clone())
            }
            (RankingMeasureValue::Integer(post), RankingMeasureValue::Integer(pre)) => {
                ConditionTerm::integer_less_than(post.clone(), pre.clone())
            }
            _ => return Err(mixed_ranking_carrier_message(component)),
        },
        true,
    ))
}

/// `post == pre`, the tie an outer lexicographic pivot stands on.
pub(super) fn ranking_tie_proposition(
    post: &RankingMeasureValue,
    pre: &RankingMeasureValue,
    component: &RankingComponent,
) -> Result<Proposition, String> {
    Ok(Proposition::ConditionIs(
        match (post, pre) {
            (RankingMeasureValue::Machine(post), RankingMeasureValue::Machine(pre))
            | (RankingMeasureValue::Unsigned32(post), RankingMeasureValue::Unsigned32(pre)) => {
                ConditionTerm::equal(post.clone(), pre.clone())
            }
            (RankingMeasureValue::Unsigned64(post), RankingMeasureValue::Unsigned64(pre)) => {
                ConditionTerm::uint64_equal(post.clone(), pre.clone())
            }
            (RankingMeasureValue::Signed64(post), RankingMeasureValue::Signed64(pre)) => {
                ConditionTerm::int64_equal(post.clone(), pre.clone())
            }
            (RankingMeasureValue::Integer(post), RankingMeasureValue::Integer(pre)) => {
                ConditionTerm::integer_equal(post.clone(), pre.clone())
            }
            _ => return Err(mixed_ranking_carrier_message(component)),
        },
        true,
    ))
}

/// The component is rendered here rather than by the caller, so a tuple pays
/// for a display string only on the refusal path.
fn mixed_ranking_carrier_message(component: &RankingComponent) -> String {
    format!(
        "the `decreases` component `{}` read in different carriers at the two states (a machine \
         int32, uint32, int64, or uint64, or a mathematical Integer), so its two values cannot be ranked \
         against each other",
        ranking_measure_display(component)
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
    state: &ExecutionState,
    reader: &mut RankingMeasureReader<'_>,
) -> Result<IntegerTerm, String> {
    let paths = crate::kernel::spec::evaluate_spec_integer_measure_paths(
        state,
        expression,
        reader.assumptions,
        reader.budget,
    )
    .map_err(|error| {
        format!(
            "could not evaluate a termination measure: it stopped at {}",
            error.describe()
        )
    })?;
    let [path] = paths.as_slice() else {
        return Err(format!(
            "a termination measure must have exactly one value at this state; this one has {}",
            paths.len()
        ));
    };
    reader.reads.obligations.extend(path.obligations.clone());
    reader.reads.facts.extend_shared(&path.facts);
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
/// int32 or unsigned integer at this state -- because the state splits it
/// into several paths, or because a view it reads is gone -- is refused
/// rather than guessed.
fn pure_ranking_measure_term(
    expression: &SpecExpression,
    state: &ExecutionState,
    reader: &mut RankingMeasureReader<'_>,
) -> Result<RankingMeasureValue, String> {
    let paths = crate::kernel::spec::evaluate_spec_expression_paths_with_loop_entry(
        state,
        expression,
        None,
        reader.assumptions,
        reader.budget,
    )
    .map_err(|error| {
        format!(
            "could not evaluate a termination measure: it stopped at {}",
            error.describe()
        )
    })?;
    let [path] = paths.as_slice() else {
        return Err(format!(
            "a termination measure must have exactly one value at this state; this one has {}",
            paths.len()
        ));
    };
    let Some(value) = RankingMachineTerm::from_value(&path.value.native()) else {
        return Err(RANKING_MEASURE_TYPE_MESSAGE.into());
    };
    reader.reads.obligations.extend(path.obligations.clone());
    reader.reads.facts.extend_shared(&path.facts);
    Ok(value.folded_measure_value())
}

/// What a machine `decreases` component must be, for every refusal of an
/// operand whose type is outside the ranked carriers.
const RANKING_MEASURE_TYPE_MESSAGE: &str = "termination measures must be int32, int64 or \
     unsigned integer (uint8, uint16, uint32, uint64) expressions";

/// The machine type C gives a measure subexpression after the integer
/// promotions: every type narrower than `int` -- `_Bool`, `int8`, `int16`,
/// `uint8`, `uint16` -- is an `int32`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RankingMachineType {
    Int32,
    UInt32,
    Int64,
    UInt64,
}

/// One measure subexpression's value and its promoted C type.
///
/// The fold computes what C computes: operands meet at the type C's usual
/// arithmetic conversions give them, so `4 - x` over a `uint32 x` is the
/// wrapped uint32 difference, and division, remainder, right shift, and
/// comparison take the signedness of that common type.
struct RankingMachineTerm {
    machine_type: RankingMachineType,
    term: MachineTerm,
}

impl RankingMachineTerm {
    fn from_value(value: &ProgramValue) -> Option<Self> {
        // An 8- or 16-bit value is ranked by its `int32` widening, which
        // keeps its value, and a `Bool` by its cast at `int32` (rule C1).
        let (machine_type, term) = match value.numeric_value() {
            ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
            ProgramValue::Bool(term) => (
                RankingMachineType::Int32,
                MachineTerm::bool_word_as(MachineIntegerType::Int32, term),
            ),
            narrow @ (ProgramValue::Int8(term)
            | ProgramValue::Int16(term)
            | ProgramValue::UInt8(term)
            | ProgramValue::UInt16(term)) => (
                RankingMachineType::Int32,
                MachineTerm::machine_integer_cast(
                    MachineIntegerType::from_program_type(narrow.program_type())?,
                    MachineIntegerType::Int32,
                    term.clone(),
                ),
            ),
            ProgramValue::Int32(term) => (RankingMachineType::Int32, term.clone()),
            ProgramValue::UInt32(term) => (RankingMachineType::UInt32, term.clone()),
            ProgramValue::Int64(term) => (RankingMachineType::Int64, term.clone()),
            ProgramValue::UInt64(term) => (RankingMachineType::UInt64, term.clone()),
            ProgramValue::Int128(_)
            | ProgramValue::UInt128(_)
            | ProgramValue::Void
            | ProgramValue::Float32(_)
            | ProgramValue::Float64(_)
            | ProgramValue::Pointer(_)
            | ProgramValue::Parameter(_) => return None,
        };
        Some(Self { machine_type, term })
    }

    /// This value converted to `target`, as C converts an integer.
    fn convert(self, target: RankingMachineType) -> MachineTerm {
        use RankingMachineType::*;
        match (self.machine_type, target) {
            (Int32 | UInt32, Int32 | UInt32) | (UInt64, UInt64) | (Int64, Int64) => self.term,
            (Int32, UInt64) => MachineTerm::uint64_from_int32(self.term),
            (UInt32, UInt64) => MachineTerm::uint64_from_32(self.term),
            // Widening to the signed type keeps the value: a signed word is
            // sign-extended and an unsigned one zero-extended.
            (Int32, Int64) => MachineTerm::int64_from_32(self.term),
            (UInt32, Int64) => MachineTerm::int64_from_uint32(self.term),
            // Between the two 64-bit types C keeps the bits.
            (Int64, UInt64) => MachineTerm::uint64_from_int64(self.term),
            (UInt64, Int64) => MachineTerm::int64_from_uint64_bits(self.term),
            (UInt64 | Int64, Int32 | UInt32) => MachineTerm::uint32_from_64(self.term),
        }
    }

    /// The common type C's usual arithmetic conversions give two promoted
    /// operands of the ranked types.
    fn common_type(left: &Self, right: &Self) -> RankingMachineType {
        use RankingMachineType::*;
        match (left.machine_type, right.machine_type) {
            (UInt64, _) | (_, UInt64) => UInt64,
            // `long` holds every `int` and every `unsigned int`.
            (Int64, _) | (_, Int64) => Int64,
            (UInt32, _) | (_, UInt32) => UInt32,
            (Int32, Int32) => Int32,
        }
    }

    /// The carrier this value ranks in. A 32-bit value is read as one affine
    /// form, so the member is a stable function of the declaration rather
    /// than of the assignment order that produced the state; the two 32-bit
    /// carriers share that form because they share wrapping arithmetic
    /// modulo 2^32.
    fn folded_measure_value(self) -> RankingMeasureValue {
        match self.machine_type {
            RankingMachineType::Int32 => {
                RankingMeasureValue::Machine(canonical_ranking_term(&self.term))
            }
            RankingMachineType::UInt32 => {
                RankingMeasureValue::Unsigned32(canonical_ranking_term(&self.term))
            }
            RankingMachineType::Int64 => RankingMeasureValue::Signed64(self.term),
            RankingMachineType::UInt64 => RankingMeasureValue::Unsigned64(self.term),
        }
    }
}

/// The value of one memory read inside a measure, at `state`.
fn ranking_measure_read(
    expression: &ProgramExpression,
    state: &ExecutionState,
    reader: &mut RankingMeasureReader<'_>,
) -> Result<RankingMachineTerm, String> {
    if matches!(
        expression,
        ProgramExpression::TypedLoad { volatile: true, .. }
    ) {
        return Err("a termination measure may not read a volatile object".into());
    }
    let paths =
        evaluate_program_expression_paths(state, expression, reader.assumptions, reader.budget)
            .map_err(|error| {
                format!(
                    "could not evaluate a termination measure's read: it stopped at {}",
                    error.describe()
                )
            })?;
    let [path] = paths.as_slice() else {
        return Err(
            "a termination measure's read must have exactly one value at this state".into(),
        );
    };
    let ExpressionOutcome::Value(value) = &path.outcome else {
        return Err(RANKING_MEASURE_TYPE_MESSAGE.into());
    };
    let Some(value) = RankingMachineTerm::from_value(value) else {
        return Err(RANKING_MEASURE_TYPE_MESSAGE.into());
    };
    reader.reads.facts.extend_shared(&path.facts);
    reader
        .reads
        .obligations
        .extend(path.obligations.iter().cloned());
    Ok(value)
}

fn ranking_measure_term_unfolded(
    expression: &ProgramExpression,
    state: &ExecutionState,
    reader: &mut RankingMeasureReader<'_>,
) -> Result<RankingMachineTerm, String> {
    use ProgramExpression::*;
    use RankingMachineType::*;
    type Operation = fn(MachineTerm, MachineTerm) -> MachineTerm;
    /// One arithmetic operator, as C applies it at each common type.
    fn binary(
        left: &ProgramExpression,
        right: &ProgramExpression,
        state: &ExecutionState,
        reader: &mut RankingMeasureReader<'_>,
        operations: (Operation, Operation, Operation, Operation),
    ) -> Result<RankingMachineTerm, String> {
        let left = ranking_measure_term_unfolded(left, state, reader)?;
        let right = ranking_measure_term_unfolded(right, state, reader)?;
        let machine_type = RankingMachineTerm::common_type(&left, &right);
        let operation = match machine_type {
            Int32 => operations.0,
            UInt32 => operations.1,
            UInt64 => operations.2,
            Int64 => operations.3,
        };
        Ok(RankingMachineTerm {
            machine_type,
            term: operation(left.convert(machine_type), right.convert(machine_type)),
        })
    }
    /// A shift has its promoted left operand's type; the count is read as a
    /// 32-bit quantity whatever its own type.
    fn shift(
        left: &ProgramExpression,
        right: &ProgramExpression,
        state: &ExecutionState,
        reader: &mut RankingMeasureReader<'_>,
        operations: (Operation, Operation),
    ) -> Result<RankingMachineTerm, String> {
        let left = ranking_measure_term_unfolded(left, state, reader)?;
        let right = ranking_measure_term_unfolded(right, state, reader)?;
        let operation = match left.machine_type {
            Int32 => operations.0,
            UInt32 => operations.1,
            UInt64 | Int64 => {
                return Err("termination measures may not shift a 64-bit value".into());
            }
        };
        let machine_type = left.machine_type;
        Ok(RankingMachineTerm {
            machine_type,
            term: operation(left.term, right.convert(UInt32)),
        })
    }
    match expression {
        Value(value) => {
            RankingMachineTerm::from_value(value).ok_or_else(|| RANKING_MEASURE_TYPE_MESSAGE.into())
        }
        Variable(name) => match state.locals().get(name) {
            Some(value) => RankingMachineTerm::from_value(&value.native()).ok_or_else(|| {
                format!(
                    "termination measure variable `{name}` does not hold an int32, int64 or \
                     unsigned integer value"
                )
            }),
            None => Err(format!(
                "termination measure references unknown variable `{name}`"
            )),
        },
        // A cast to a type narrower than `int` keeps today's reading: the
        // operand's own value, as an int32.
        Cast {
            expression,
            target_type: ProgramType::Int32 | ProgramType::UInt8,
            ..
        } => {
            let value = ranking_measure_term_unfolded(expression, state, reader)?;
            Ok(RankingMachineTerm {
                machine_type: Int32,
                term: value.convert(Int32),
            })
        }
        Cast {
            expression,
            target_type: target @ (ProgramType::UInt32 | ProgramType::UInt64 | ProgramType::Int64),
            ..
        } => {
            let machine_type = match target {
                ProgramType::UInt32 => UInt32,
                ProgramType::Int64 => Int64,
                _ => UInt64,
            };
            let value = ranking_measure_term_unfolded(expression, state, reader)?;
            Ok(RankingMachineTerm {
                machine_type,
                term: value.convert(machine_type),
            })
        }
        EnumConstruct { .. } | EnumField { .. } | EnumIs { .. } => {
            Err("termination measures may not read Rust enum values".into())
        }
        StepResult { .. } => Err("termination measures may not read a call's result".into()),
        Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            let (condition, value) = ranking_measure_condition_term(condition, state, reader)?;
            let then_value = ranking_measure_term_unfolded(then_branch, state, reader)?;
            let else_value = ranking_measure_term_unfolded(else_branch, state, reader)?;
            let machine_type = RankingMachineTerm::common_type(&then_value, &else_value);
            if matches!(machine_type, UInt64 | Int64) {
                return Err(
                    "termination measures may not choose between 64-bit values with `?:`".into(),
                );
            }
            let (then_term, else_term) = if value {
                (
                    then_value.convert(machine_type),
                    else_value.convert(machine_type),
                )
            } else {
                (
                    else_value.convert(machine_type),
                    then_value.convert(machine_type),
                )
            };
            Ok(RankingMachineTerm {
                machine_type,
                term: MachineTerm::If {
                    condition: Box::new(condition),
                    then_term: Box::new(then_term),
                    else_term: Box::new(else_term),
                },
            })
        }
        Add(left, right) => binary(
            left,
            right,
            state,
            reader,
            (
                MachineTerm::add,
                MachineTerm::add,
                MachineTerm::uint64_add,
                MachineTerm::int64_add,
            ),
        ),
        Subtract(left, right) => binary(
            left,
            right,
            state,
            reader,
            (
                MachineTerm::subtract,
                MachineTerm::subtract,
                MachineTerm::uint64_subtract,
                MachineTerm::int64_subtract,
            ),
        ),
        Multiply(left, right) => binary(
            left,
            right,
            state,
            reader,
            (
                MachineTerm::multiply,
                MachineTerm::multiply,
                MachineTerm::uint64_multiply,
                MachineTerm::int64_multiply,
            ),
        ),
        Divide(left, right) => binary(
            left,
            right,
            state,
            reader,
            (
                MachineTerm::divide,
                MachineTerm::unsigned_divide,
                MachineTerm::uint64_divide,
                MachineTerm::int64_divide,
            ),
        ),
        Remainder(left, right) => binary(
            left,
            right,
            state,
            reader,
            (
                MachineTerm::remainder,
                MachineTerm::unsigned_remainder,
                MachineTerm::uint64_remainder,
                MachineTerm::int64_remainder,
            ),
        ),
        RustShiftLeft(..) | RustShiftRight(..) => ranking_measure_read(expression, state, reader),
        ShiftLeft(left, right) => shift(
            left,
            right,
            state,
            reader,
            (MachineTerm::shift_left, MachineTerm::shift_left),
        ),
        ShiftRight(left, right) => shift(
            left,
            right,
            state,
            reader,
            (
                MachineTerm::arithmetic_shift_right,
                MachineTerm::logical_shift_right,
            ),
        ),
        BitwiseAnd(left, right) => binary(
            left,
            right,
            state,
            reader,
            (
                MachineTerm::bitwise_and,
                MachineTerm::bitwise_and,
                MachineTerm::uint64_bitwise_and,
                MachineTerm::uint64_bitwise_and,
            ),
        ),
        BitwiseOr(left, right) => binary(
            left,
            right,
            state,
            reader,
            (
                MachineTerm::bitwise_or,
                MachineTerm::bitwise_or,
                MachineTerm::uint64_bitwise_or,
                MachineTerm::uint64_bitwise_or,
            ),
        ),
        BitwiseXor(left, right) => binary(
            left,
            right,
            state,
            reader,
            (
                MachineTerm::bitwise_xor,
                MachineTerm::bitwise_xor,
                MachineTerm::uint64_bitwise_xor,
                MachineTerm::uint64_bitwise_xor,
            ),
        ),
        BitwiseNot(value) => {
            let value = ranking_measure_term_unfolded(value, state, reader)?;
            let machine_type = value.machine_type;
            let term = if matches!(machine_type, UInt64 | Int64) {
                MachineTerm::uint64_bitwise_not(value.term)
            } else {
                MachineTerm::bitwise_not(value.term)
            };
            Ok(RankingMachineTerm { machine_type, term })
        }
        Cast { .. }
        | FloatNegate(_)
        | FloatClassification { .. }
        | FunctionAddress(_)
        | AddressOf(_)
        | CheckedObjectAddress(_)
        | PointerOffsetBytes { .. }
        | Subobject { .. } => Err(
            "termination measures may only use scalar int32 or unsigned integer expressions".into(),
        ),
        Load(_) | TypedLoad { .. } | Index(_, _) => ranking_measure_read(expression, state, reader),
        LessThan(_, _)
        | LessEqual(_, _)
        | GreaterThan(_, _)
        | GreaterEqual(_, _)
        | Equal(_, _)
        | NotEqual(_, _)
        | Not(_)
        | And(_, _)
        | Or(_, _) => {
            Err("termination measures must have an integer value, not a truth value".into())
        }
    }
}

fn ranking_measure_condition_term(
    expression: &ProgramExpression,
    state: &ExecutionState,
    reader: &mut RankingMeasureReader<'_>,
) -> Result<(ConditionTerm, bool), String> {
    use ProgramExpression::*;
    use RankingMachineType::*;
    /// The relation `left < right` (or `<=`, or `==`) at the operands' common
    /// type, so an unsigned pair compares as C compares it.
    #[derive(Clone, Copy)]
    enum Relation {
        Less,
        LessEqual,
        Greater,
        GreaterEqual,
        Equal,
    }
    fn compare(
        left: &ProgramExpression,
        right: &ProgramExpression,
        state: &ExecutionState,
        reader: &mut RankingMeasureReader<'_>,
        relation: Relation,
    ) -> Result<ConditionTerm, String> {
        let left = ranking_measure_term_unfolded(left, state, reader)?;
        let right = ranking_measure_term_unfolded(right, state, reader)?;
        let machine_type = RankingMachineTerm::common_type(&left, &right);
        let (left, right) = (left.convert(machine_type), right.convert(machine_type));
        Ok(match (machine_type, relation) {
            (Int32, Relation::Less) => ConditionTerm::signed_less_than(left, right),
            (Int32, Relation::LessEqual) => ConditionTerm::signed_less_equal(left, right),
            (Int32, Relation::Greater) => ConditionTerm::signed_greater_than(left, right),
            (Int32, Relation::GreaterEqual) => ConditionTerm::signed_greater_equal(left, right),
            (UInt32, Relation::Less) => ConditionTerm::unsigned_less_than(left, right),
            (UInt32, Relation::LessEqual) => ConditionTerm::unsigned_less_equal(left, right),
            (UInt32, Relation::Greater) => ConditionTerm::unsigned_less_than(right, left),
            (UInt32, Relation::GreaterEqual) => ConditionTerm::unsigned_less_equal(right, left),
            (Int32 | UInt32, Relation::Equal) => ConditionTerm::equal(left, right),
            (UInt64, Relation::Less) => ConditionTerm::uint64_less_than(left, right),
            (UInt64, Relation::LessEqual) => ConditionTerm::uint64_less_equal(left, right),
            (UInt64, Relation::Greater) => ConditionTerm::uint64_less_than(right, left),
            (UInt64, Relation::GreaterEqual) => ConditionTerm::uint64_less_equal(right, left),
            (UInt64, Relation::Equal) => ConditionTerm::uint64_equal(left, right),
            (Int64, Relation::Less) => ConditionTerm::int64_signed_less_than(left, right),
            (Int64, Relation::LessEqual) => ConditionTerm::int64_signed_less_equal(left, right),
            (Int64, Relation::Greater) => ConditionTerm::int64_signed_less_than(right, left),
            (Int64, Relation::GreaterEqual) => ConditionTerm::int64_signed_less_equal(right, left),
            (Int64, Relation::Equal) => ConditionTerm::int64_equal(left, right),
        })
    }
    match expression {
        LessThan(left, right) => Ok((compare(left, right, state, reader, Relation::Less)?, true)),
        LessEqual(left, right) => Ok((
            compare(left, right, state, reader, Relation::LessEqual)?,
            true,
        )),
        GreaterThan(left, right) => Ok((
            compare(left, right, state, reader, Relation::Greater)?,
            true,
        )),
        GreaterEqual(left, right) => Ok((
            compare(left, right, state, reader, Relation::GreaterEqual)?,
            true,
        )),
        Equal(left, right) => Ok((compare(left, right, state, reader, Relation::Equal)?, true)),
        NotEqual(left, right) => Ok((compare(left, right, state, reader, Relation::Equal)?, false)),
        Not(inner) => {
            let (condition, value) = ranking_measure_condition_term(inner, state, reader)?;
            Ok((condition, !value))
        }
        And(_, _) | Or(_, _) => {
            Err("compound boolean conditions are not atomic ranking measure conditions".into())
        }
        _ => {
            let value = ranking_measure_term_unfolded(expression, state, reader)?;
            Ok((
                if matches!(value.machine_type, UInt64 | Int64) {
                    ConditionTerm::uint64_equal(value.term, MachineTerm::uint64_constant(0))
                } else {
                    ConditionTerm::equal(value.term, MachineTerm::constant(0))
                },
                false,
            ))
        }
    }
}

/// The recursion anchor for one C function at its own entry state, or `None`
/// when the function declares no expression `decreases` measure.
///
/// This is the only construction of a [`RecursionAnchor`]. The measure is
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
pub(super) fn program_function_recursion_anchor(
    function: &ProgramFunction,
    entry_state: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Result<Option<RecursionAnchor>, String> {
    let interface = function.contract_interface();
    if let Some(binder) = interface.recursion_binder() {
        // A structural measure is the instance the binder holds at entry; the
        // descent at each call compares the instance it passes with this one.
        let identity = interface.resource_binder_identity(binder).ok_or_else(|| {
            format!(
                "the `decreases {binder}` measure of `{}` names no resource binder of its \
                 contract",
                function.name()
            )
        })?;
        let entry = entry_state
            .resources()
            .owned_instance(identity)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "the `decreases {binder}` measure of `{}` names a binder with no owned \
                     instance at the function's entry",
                    function.name()
                )
            })?;
        return Ok(Some(RecursionAnchor {
            function: function.name().to_string(),
            components: Vec::new(),
            peers: interface.recursion_peers().to_vec(),
            measure: Vec::new(),
            structural_entry: Some(entry),
            entry_obligations: Vec::new(),
        }));
    }
    let Some(components) = interface.recursion_measure() else {
        return Ok(None);
    };
    let mut reader = RankingMeasureReader {
        assumptions,
        budget,
        reads: Default::default(),
    };
    let measure = components
        .iter()
        .map(|component| {
            ranking_measure_term(component, entry_state, &mut reader).map_err(|error| {
                format!(
                    "the `decreases` measure `{}` of `{}` could not be read at its own entry \
                     state: {error}",
                    ranking_measure_display(component),
                    function.name()
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
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
    Ok(Some(RecursionAnchor {
        function: function.name().to_string(),
        components: components.to_vec(),
        peers: function.contract_interface().recursion_peers().to_vec(),
        measure,
        structural_entry: None,
        entry_obligations,
    }))
}

/// The ranking members one call to a member of the anchor's component owes,
/// against the anchor's M0.
///
/// `components` is the callee's declared measure: the anchor's own for a
/// self-call, a peer's for a call to another member, whose tuple must have the
/// anchor's length and, position by position, its carrier. Every member's
/// measure then lies in one lexicographic order, and a chain of calls through
/// the component descends in it whichever member each call reaches.
///
/// The callee's declared measure is read at `state`, the same state the
/// callee's preconditions are read at, so the parameters it names hold the
/// arguments this call passes and a read it performs sees the memory the
/// callee will see. The members are the function-level form of the loop's
/// back-edge bundle: each component of the callee's measure is nonnegative,
/// and the tuple is lexicographically below the value the caller's own entry
/// gave. A recursion whose every step satisfies both cannot be infinite,
/// whatever the measure counts.
pub(super) fn collect_recursion_descent_obligations(
    anchor: &RecursionAnchor,
    callee: &str,
    components: &[RankingComponent],
    state: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Result<Vec<ProofObligation>, String> {
    if components.len() != anchor.measure().len() {
        return Err(format!(
            "`{callee}`'s `decreases` measure `{}` has {} components, but `{}`'s has {}; the \
             members of a recursive component must declare measures of one shape",
            ranking_measures_display(components),
            components.len(),
            anchor.function(),
            anchor.measure().len()
        ));
    }
    let mut reader = RankingMeasureReader {
        assumptions,
        budget,
        reads: Default::default(),
    };
    let called = components
        .iter()
        .map(|component| {
            ranking_measure_term(component, state, &mut reader).map_err(|error| {
                format!(
                    "the `decreases` measure `{}` of `{callee}` could not be read at the recursive \
                     call: {error}",
                    ranking_measure_display(component)
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
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
    for (component, called) in components.iter().zip(&called) {
        obligations.push(
            ProofObligation::verification_condition(ranking_nonnegative_proposition(called))
                .with_introductions(LoweringIntroductions::new())
                .with_context(format!(
                    "{context}: `{}` is nonnegative at the recursive call",
                    ranking_measure_display(component)
                )),
        );
    }
    obligations.push(
        ProofObligation::verification_condition(ranking_lexicographic_decrease_proposition(
            &called,
            anchor.measure(),
            components,
        )?)
        .with_introductions(LoweringIntroductions::new())
        .with_context(format!(
            "{context}: `{}` decreases at the recursive call",
            ranking_measures_display(components)
        )),
    );
    Ok(obligations)
}

/// `post <lex pre` for two readings of one declared tuple: some pivot
/// component is strictly smaller and every earlier component is tied. It is
/// the right-nested disjunction over pivots, so a one-component measure is
/// exactly that component's `post < pre`.
///
/// A pivot arm compares one component's two readings, never two different
/// components, so a tuple whose components chose different carriers needs
/// no coercion: each arm is built in its own component's carrier. Work is
/// quadratic in the declared tuple's length, which the source fixes.
pub(super) fn ranking_lexicographic_decrease_proposition(
    post: &[RankingMeasureValue],
    pre: &[RankingMeasureValue],
    components: &[RankingComponent],
) -> Result<Proposition, String> {
    let arm = |pivot: usize| -> Result<Proposition, String> {
        let strict = ranking_decrease_proposition(&post[pivot], &pre[pivot], &components[pivot])?;
        (0..pivot).rev().try_fold(strict, |rest, index| {
            Ok(Proposition::And(
                Box::new(ranking_tie_proposition(
                    &post[index],
                    &pre[index],
                    &components[index],
                )?),
                Box::new(rest),
            ))
        })
    };
    (0..components.len())
        .rev()
        .try_fold(None, |rest: Option<Proposition>, pivot| {
            Ok::<_, String>(match rest {
                None => Some(arm(pivot)?),
                Some(rest) => Some(Proposition::Or(Box::new(arm(pivot)?), Box::new(rest))),
            })
        })?
        .ok_or_else(|| "a `decreases` measure declares at least one component".to_string())
}

/// The display form of one `decreases` component, for bundle member contexts.
pub(super) fn ranking_measure_display(measure: &RankingComponent) -> String {
    match measure {
        RankingComponent::ProgramExpression(expression) => termination_measure_display(expression),
        // A pure component is shown as it was declared: its lowered form is a
        // specification tree with no source spelling of its own.
        RankingComponent::Pure { source, .. } | RankingComponent::PureInteger { source, .. } => {
            source.clone()
        }
    }
}

/// The display form of a whole `decreases` clause.
pub(super) fn ranking_measures_display(measures: &[RankingComponent]) -> String {
    join_measure_components(measures.iter().map(ranking_measure_display))
}

/// The identity spelling of one `decreases` component: what a pure
/// component's written source is built from and compared with (see
/// [`termination_measure_key`]).
pub(super) fn ranking_measure_key(measure: &RankingComponent) -> String {
    match measure {
        RankingComponent::ProgramExpression(expression) => termination_measure_key(expression),
        RankingComponent::Pure { source, .. } | RankingComponent::PureInteger { source, .. } => {
            source.clone()
        }
    }
}

/// Whether a certified loop measure and the plan's measure name one
/// declaration. They are equal keys, except that a component naming a proof
/// binder (a proof `match` payload or a `let { field: name } = unfold(...)`
/// name) resolves at the loop head to the value it stands for and is carried
/// as a pure component under its written spelling, while the plan, built from
/// the written clause before any proof runs, reads that spelling as C. As the
/// `RankingMeasureKey` documentation explains, this comparison identifies a
/// declaration; the termination evidence is the certified back-edge bundle.
fn loop_measures_name_same_declaration(
    certified: &LoopTerminationMeasure,
    planned: &LoopTerminationMeasure,
) -> bool {
    match (certified, planned) {
        (LoopTerminationMeasure::Ranking(certified), LoopTerminationMeasure::Ranking(planned)) => {
            certified.len() == planned.len()
                && certified.iter().zip(planned).all(|(certified, planned)| {
                    match (certified, planned) {
                        (
                            RankingMeasureKey::Pure(source),
                            RankingMeasureKey::ProgramExpression(written),
                        ) => *source == termination_measure_key(written),
                        (certified, planned) => certified == planned,
                    }
                })
        }
        (certified, planned) => certified == planned,
    }
}

/// The display form of one loop's declared measure, for plan diagnostics.
fn loop_termination_measure_display(measure: &LoopTerminationMeasure) -> String {
    match measure {
        LoopTerminationMeasure::Ranking(measures) => {
            join_measure_components(measures.iter().map(|measure| match measure {
                RankingMeasureKey::ProgramExpression(expression) => {
                    termination_measure_display(expression)
                }
                RankingMeasureKey::Pure(source) => source.clone(),
            }))
        }
        LoopTerminationMeasure::Structural(binder) => binder.clone(),
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

/// The function's loops in the order `check_loops` numbers them: a loop
/// before the loops in its body, then the rest in source order. One walk,
/// so looking up every verified loop rule costs the function once.
fn loops_in_order(statement: &ProgramStatement) -> Vec<&ProgramStatement> {
    let mut loops = Vec::new();
    collect_loops_in_order(statement, &mut loops);
    loops
}

fn collect_loops_in_order<'a>(
    statement: &'a ProgramStatement,
    loops: &mut Vec<&'a ProgramStatement>,
) {
    charge_termination_work(1);
    match statement {
        ProgramStatement::While { body, .. } => {
            loops.push(statement);
            collect_loops_in_order(body, loops);
        }
        ProgramStatement::Seq(statements) => {
            charge_seq_spine(statements);
            for statement in statements.iter() {
                collect_loops_in_order(statement, loops);
            }
        }
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_loops_in_order(then_branch, loops);
            collect_loops_in_order(else_branch, loops);
        }
        ProgramStatement::Switch { cases, .. } => {
            for case in cases {
                collect_loops_in_order(&case.body, loops);
            }
        }
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            collect_loops_in_order(try_body, loops);
            collect_loops_in_order(handler, loops);
        }
        ProgramStatement::ForStep { step, .. } => collect_loops_in_order(step, loops),
        // Spelled out, as in `check_loops`: the two walks number the same
        // loops only while they descend into the same statements, so a new
        // statement kind must be placed in both.
        ProgramStatement::Skip
        | ProgramStatement::EndScalarReference(_)
        | ProgramStatement::ScalarReferenceScope(_)
        | ProgramStatement::EndAutomaticLifetimes { .. }
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::Declare { .. }
        | ProgramStatement::DeclareAggregate { .. }
        | ProgramStatement::Assign { .. }
        | ProgramStatement::CallConstruct { .. }
        | ProgramStatement::Call { .. }
        | ProgramStatement::CallResult { .. }
        | ProgramStatement::HeapAllocate { .. }
        | ProgramStatement::HeapFree { .. }
        | ProgramStatement::Assert { .. }
        | ProgramStatement::StepValue { .. }
        | ProgramStatement::LoopTest { .. }
        | ProgramStatement::Throw(_)
        | ProgramStatement::Return(_)
        | ProgramStatement::Store { .. }
        | ProgramStatement::TypedStore { .. }
        | ProgramStatement::CopyAggregate { .. }
        | ProgramStatement::InitializeScalarArray { .. }
        | ProgramStatement::Update { .. } => {}
    }
}

/// Compares two C statements while ignoring proof annotations. A verified
/// frontier rule may carry nested invariant checks that the partial function
/// used for contract certification intentionally omits; its executable shape
/// must still be the exact loop shape from the source body.
fn same_statement_shape(left: &ProgramStatement, right: &ProgramStatement) -> bool {
    match (left, right) {
        (ProgramStatement::Seq(left), ProgramStatement::Seq(right)) => {
            same_statement_shape(left.first(), right.first())
                && same_statement_shape(&left.rest(), &right.rest())
        }
        (
            ProgramStatement::If {
                condition: left_condition,
                then_branch: left_then,
                else_branch: left_else,
            },
            ProgramStatement::If {
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
            ProgramStatement::While {
                condition: left_condition,
                do_while: left_do_while,
                body: left_body,
                ..
            },
            ProgramStatement::While {
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
            ProgramStatement::Switch {
                expression: left_expression,
                cases: left_cases,
            },
            ProgramStatement::Switch {
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
            ProgramStatement::ForStep {
                step: left_step,
                exited_locals: left_locals,
                continue_after: left_continue,
            },
            ProgramStatement::ForStep {
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
    source_body: &ProgramStatement,
    rules: &[VerifiedLoopRule],
) -> Result<
    (
        BTreeMap<usize, Vec<LoopTerminationMeasure>>,
        BTreeSet<usize>,
    ),
    TerminationError,
> {
    let mut certified: BTreeMap<usize, Vec<LoopTerminationMeasure>> = BTreeMap::new();
    let mut unranked = BTreeSet::new();
    let loops = loops_in_order(source_body);
    let addressed = address_taken_locals(source_body);
    for rule in rules {
        charge_termination_work(1);
        let Some(index) = rule.loop_index else {
            continue;
        };
        let Some(&source_loop) = loops.get(index) else {
            return Err(error(format!(
                "verified loop rule for `{function_name}` refers to nonexistent loop {index}"
            )));
        };
        if !same_statement_shape(source_loop, &rule.loop_statement) {
            return Err(error(format!(
                "verified loop rule for `{function_name}` does not match loop {index}'s source shape"
            )));
        }
        let ProgramStatement::While {
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
            reject_address_escaped_ranking_component(function_name, component, &addressed)?;
        }
        let measure = match structural_measure {
            Some(binder) => LoopTerminationMeasure::Structural(binder.clone()),
            None if ranking_measures.is_empty() => {
                unranked.insert(index);
                continue;
            }
            None => LoopTerminationMeasure::Ranking(
                ranking_measures.iter().map(RankingComponent::key).collect(),
            ),
        };
        // Each strategy owns the measure checked by its own back-edge proof.
        // Different strategies for this source loop need not share a measure.
        certified.entry(index).or_default().push(measure);
    }
    // Termination needs every summarized path to carry a ranking proof. A
    // ranked sibling cannot stand in for an unranked execution of this loop.
    for index in &unranked {
        certified.remove(index);
    }
    Ok((certified, unranked))
}

fn ranking_affine_form(term: &MachineTerm) -> (BTreeMap<MachineTerm, i64>, i64) {
    match term {
        bits32_constant!(value) => (BTreeMap::new(), i64::from(constant_u32(*value) as i32)),
        binary_term!(Int32, Add, left, right) => {
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
        binary_term!(Int32, Subtract, left, right) => {
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
        binary_term!(Int32, Multiply, left, right) => {
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

fn canonical_ranking_term(term: &MachineTerm) -> MachineTerm {
    let (terms, constant) = ranking_affine_form(term);
    let mut result = MachineTerm::constant(0);
    for (term, coefficient) in terms {
        let magnitude = coefficient.unsigned_abs();
        let factor = if magnitude == 1 {
            term
        } else {
            MachineTerm::multiply(MachineTerm::constant(magnitude as u32), term)
        };
        result = if coefficient < 0 {
            MachineTerm::subtract(result, factor)
        } else {
            MachineTerm::add(result, factor)
        };
    }
    if constant < 0 {
        MachineTerm::subtract(
            result,
            MachineTerm::constant(constant.unsigned_abs() as u32),
        )
    } else {
        MachineTerm::add(result, MachineTerm::constant(constant as u32))
    }
}

/// Every loop of `statement`, in the order `check_loops` numbers them.
fn collect_loops<'a>(statement: &'a ProgramStatement, loops: &mut Vec<&'a ProgramStatement>) {
    charge_termination_work(1);
    match statement {
        ProgramStatement::While { body, .. } => {
            loops.push(statement);
            collect_loops(body, loops);
        }
        ProgramStatement::Seq(statements) => {
            charge_seq_spine(statements);
            for statement in statements.iter() {
                collect_loops(statement, loops);
            }
        }
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_loops(then_branch, loops);
            collect_loops(else_branch, loops);
        }
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            collect_loops(try_body, loops);
            collect_loops(handler, loops);
        }
        ProgramStatement::Switch { cases, .. } => {
            for case in cases {
                collect_loops(&case.body, loops);
            }
        }
        ProgramStatement::ForStep { step, .. } => collect_loops(step, loops),
        ProgramStatement::Skip
        | ProgramStatement::EndScalarReference(_)
        | ProgramStatement::ScalarReferenceScope(_)
        | ProgramStatement::EndAutomaticLifetimes { .. }
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::Declare { .. }
        | ProgramStatement::DeclareAggregate { .. }
        | ProgramStatement::Assign { .. }
        | ProgramStatement::CallConstruct { .. }
        | ProgramStatement::Call { .. }
        | ProgramStatement::CallResult { .. }
        | ProgramStatement::HeapAllocate { .. }
        | ProgramStatement::HeapFree { .. }
        | ProgramStatement::Assert { .. }
        | ProgramStatement::StepValue { .. }
        | ProgramStatement::LoopTest { .. }
        | ProgramStatement::Throw(_)
        | ProgramStatement::Return(_)
        | ProgramStatement::Store { .. }
        | ProgramStatement::TypedStore { .. }
        | ProgramStatement::CopyAggregate { .. }
        | ProgramStatement::InitializeScalarArray { .. }
        | ProgramStatement::Update { .. } => {}
    }
}

/// The loops of a certified function that certification executed to their
/// exit, by source index.
///
/// A verified loop rule can summarize a loop even when its clause carries no
/// checks. Exclude every loop named by a rule before considering empty
/// annotations as evidence of concrete execution. An unruled loop with no
/// checks or measure takes the concrete route, one budgeted iteration at a
/// time, and returns only when every feasible path has left it.
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
    function: &ProgramFunction,
    loop_semantics: LoopSemantics,
    ruled_loops: &BTreeSet<usize>,
) -> BTreeSet<usize> {
    let source_body = if contains_natural_control_loop(function.body()) {
        function.body()
    } else {
        &function.source_body
    };
    let mut source_loops = Vec::new();
    collect_loops(source_body, &mut source_loops);
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
            if ruled_loops.contains(index) {
                return false;
            }
            let ProgramStatement::While {
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
                .all(|check| check.origin() == LoopEffectOrigin::InheritedResourceDerived)
                && loop_semantics == LoopSemantics::ApplyVerifiedRules
        })
        .map(|(index, _)| index)
        .collect()
}

fn contains_natural_control_loop(statement: &ProgramStatement) -> bool {
    match statement {
        ProgramStatement::While {
            backedge_target: Some(_),
            ..
        } => true,
        ProgramStatement::Seq(statements) => statements
            .iter()
            .any(|statement| contains_natural_control_loop(statement)),
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            contains_natural_control_loop(then_branch) || contains_natural_control_loop(else_branch)
        }
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        } => contains_natural_control_loop(try_body) || contains_natural_control_loop(handler),
        ProgramStatement::Switch { cases, .. } => cases
            .iter()
            .any(|case| contains_natural_control_loop(&case.body)),
        ProgramStatement::ForStep { step, .. } => contains_natural_control_loop(step),
        _ => false,
    }
}

/// Confirms that every loop the plan ranks has a checked back-edge bundle
/// for exactly that measure, and collects the index of every loop that
/// carries no measure at all. Every loop is visited, so the collected indices
/// and `next_index` describe the whole statement whichever loops are ranked.
///
/// This pass proves nothing. A loop's nonnegativity and lexicographic
/// decrease obligations are members of its `close_invariants` bundle, which
/// the loop's own verified rule already certified; the rule carries the
/// declared measure on its loop head. Every strategy owns its own ranking;
/// an optional plan names one of them, without constraining its siblings.
#[cfg(test)]
fn check_loops(
    statement: &ProgramStatement,
    supplied: &BTreeMap<usize, LoopTerminationMeasure>,
    certified: &BTreeMap<usize, Vec<LoopTerminationMeasure>>,
    function_name: &str,
    next_index: &mut usize,
    unranked: &mut Vec<usize>,
) -> Result<(), TerminationError> {
    visit_loop_obligations(statement, next_index, &mut |index| {
        prove_loop_obligation(index, supplied, certified, function_name, unranked)
    })
}

/// Allocate source loop identities in the existing order, without checking a
/// ranking proof. Children precede their parent in proof execution order.
fn visit_loop_obligations(
    statement: &ProgramStatement,
    next_index: &mut usize,
    visit: &mut impl FnMut(usize) -> Result<(), TerminationError>,
) -> Result<(), TerminationError> {
    charge_termination_work(1);
    match statement {
        ProgramStatement::Seq(statements) => {
            visit_loop_obligations(statements.first(), next_index, visit)?;
            visit_loop_obligations(&statements.rest(), next_index, visit)
        }
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            visit_loop_obligations(then_branch, next_index, visit)?;
            visit_loop_obligations(else_branch, next_index, visit)
        }
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            visit_loop_obligations(try_body, next_index, visit)?;
            visit_loop_obligations(handler, next_index, visit)
        }
        ProgramStatement::While { body, .. } => {
            let index = *next_index;
            *next_index += 1;
            visit_loop_obligations(body, next_index, visit)?;
            visit(index)
        }
        ProgramStatement::Switch { cases, .. } => {
            for case in cases {
                visit_loop_obligations(&case.body, next_index, visit)?;
            }
            Ok(())
        }
        ProgramStatement::ForStep { step, .. } => visit_loop_obligations(step, next_index, visit),
        ProgramStatement::Skip
        | ProgramStatement::EndScalarReference(_)
        | ProgramStatement::ScalarReferenceScope(_)
        | ProgramStatement::EndAutomaticLifetimes { .. }
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::Declare { .. }
        | ProgramStatement::DeclareAggregate { .. }
        | ProgramStatement::Assign { .. }
        | ProgramStatement::CallConstruct { .. }
        | ProgramStatement::Call { .. }
        | ProgramStatement::CallResult { .. }
        | ProgramStatement::HeapAllocate { .. }
        | ProgramStatement::HeapFree { .. }
        | ProgramStatement::Assert { .. }
        | ProgramStatement::StepValue { .. }
        | ProgramStatement::LoopTest { .. }
        | ProgramStatement::Throw(_)
        | ProgramStatement::Return(_)
        | ProgramStatement::Store { .. }
        | ProgramStatement::TypedStore { .. }
        | ProgramStatement::CopyAggregate { .. }
        | ProgramStatement::InitializeScalarArray { .. }
        | ProgramStatement::Update { .. } => Ok(()),
    }
}

/// Discharge one previously generated loop-ranking requirement.
fn prove_loop_obligation(
    index: usize,
    supplied: &BTreeMap<usize, LoopTerminationMeasure>,
    certified: &BTreeMap<usize, Vec<LoopTerminationMeasure>>,
    function_name: &str,
    unranked: &mut Vec<usize>,
) -> Result<(), TerminationError> {
    charge_termination_work(1);
    // Frontier-local proofs already certify their ranking components on
    // the exact source loop. They need no speculative syntax-order
    // plan; explicit plans remain demands checked against that rule.
    let Some(measures) = supplied
        .get(&index)
        .or_else(|| certified.get(&index)?.first())
    else {
        unranked.push(index);
        return Ok(());
    };
    if matches!(measures, LoopTerminationMeasure::Ranking(components) if components.is_empty()) {
        return Err(error(format!(
            "loop {index} has an empty termination measure"
        )));
    }
    match certified.get(&index) {
        Some(checked)
            if checked.iter().any(|owned| {
                charge_termination_work(1);
                loop_measures_name_same_declaration(owned, measures)
            }) =>
        {
            Ok(())
        }
        Some(checked) => Err(error(format!(
            "loop {index} in `{function_name}` was certified for `{}`, not the planned `{}`",
            checked
                .iter()
                .map(loop_termination_measure_display)
                .collect::<Vec<_>>()
                .join("` or `"),
            loop_termination_measure_display(measures)
        ))),
        None => Err(error(format!(
            "loop {index} in `{function_name}` has no verified loop rule carrying its \
             `decreases` measure, so its back-edge ranking obligations were never checked"
        ))),
    }
}

/// Union each shared dependency set once at a certification boundary. Missing
/// evidence is contagious: it must never be interpreted as an empty call set.
pub(in crate::kernel) fn merge_checked_callees<'a>(
    sets: impl IntoIterator<Item = Option<&'a Arc<BTreeSet<String>>>>,
) -> Option<Arc<BTreeSet<String>>> {
    let mut unique = BTreeMap::new();
    for set in sets {
        charge_termination_work(1);
        let set = set?;
        unique.entry(Arc::as_ptr(set) as usize).or_insert(set);
    }
    if unique.is_empty() {
        return None;
    }
    if unique.len() == 1 {
        return Some((*unique.values().next().unwrap()).clone());
    }
    let mut combined = BTreeSet::new();
    for set in unique.values() {
        charge_termination_work(set.len());
        combined.extend(set.iter().cloned());
    }
    Some(Arc::new(combined))
}

/// The callees of one body, with a callee spelled like an object the function
/// binds recorded under a name no function can have.
///
/// C11 6.2.1p4 hides a file-scope function of the same name behind a
/// parameter or local, so such a call goes through that object. Resolving it
/// to the function would hand the call that function's ranking proof, so it is
/// left unranked, which is the treatment every indirect call gets.
fn termination_callees(function: &ProgramFunction) -> BTreeSet<String> {
    let mut found = BTreeSet::new();
    statement_calls(&function.source_body, &mut found);
    classify_termination_callees(function, found.into_iter())
}

fn classify_termination_callees(
    function: &ProgramFunction,
    found: impl Iterator<Item = String>,
) -> BTreeSet<String> {
    let objects = function_object_names(function);
    found
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
    function: &ProgramFunction,
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
            SpecProposition::Predicate {
                name, arguments, ..
            } => {
                let Some(contract) = FunctionContract::surface_name_from_predicate(name) else {
                    return;
                };
                if !diverging_contracts.contains(contract) {
                    return;
                }
                // The function value comes first; any values after it fix
                // the contract's value parameters.
                let [
                    SpecPredicateArgument::Value(SpecExpression::ProgramExpression(
                        ProgramExpression::Variable(object),
                    )),
                    ..,
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
fn value_function_address(value: &ProgramValue) -> Option<&str> {
    let ProgramValue::Pointer(pointer) = value else {
        return None;
    };
    match &pointer.pointer().block {
        PointerBlock::Function(name) => Some(name),
        _ => None,
    }
}

fn expression_function_addresses(expression: &ProgramExpression, taken: &mut BTreeSet<String>) {
    use ProgramExpression::*;
    match expression {
        FunctionAddress(name) => {
            taken.insert(name.clone());
        }
        Value(value) => {
            if let Some(name) = value_function_address(value) {
                taken.insert(name.to_string());
            }
        }
        Variable(_) | StepResult { .. } => {}
        Cast { expression, .. }
        | FloatNegate(expression)
        | FloatClassification { expression, .. }
        | EnumField {
            value: expression, ..
        }
        | EnumIs {
            value: expression, ..
        }
        | AddressOf(expression)
        | CheckedObjectAddress(expression)
        | PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | Subobject {
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
        EnumConstruct { fields, .. } => {
            for field in fields {
                expression_function_addresses(field, taken);
            }
        }
        Ternary {
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
        | RustShiftLeft(left, right)
        | RustShiftRight(left, right)
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

fn statement_function_addresses(statement: &ProgramStatement, taken: &mut BTreeSet<String>) {
    charge_termination_work(1);
    let mut visit =
        |expression: &ProgramExpression| expression_function_addresses(expression, taken);
    match statement {
        ProgramStatement::Skip
        | ProgramStatement::EndScalarReference(_)
        | ProgramStatement::ScalarReferenceScope(_)
        | ProgramStatement::EndAutomaticLifetimes { .. }
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::Declare {
            initializer: None, ..
        }
        | ProgramStatement::DeclareAggregate { .. } => {}
        ProgramStatement::Declare {
            initializer: Some(expression),
            ..
        }
        | ProgramStatement::Assign { expression, .. }
        | ProgramStatement::Return(expression)
        | ProgramStatement::Throw(expression) => visit(expression),
        ProgramStatement::CallConstruct { arguments, .. }
        | ProgramStatement::Call { arguments, .. }
        | ProgramStatement::CallResult { arguments, .. } => {
            arguments.iter().for_each(visit);
        }
        ProgramStatement::HeapAllocate { bytes, .. } => visit(bytes),
        ProgramStatement::HeapFree { pointer } => visit(pointer),
        ProgramStatement::Assert { condition, .. }
        | ProgramStatement::LoopTest { condition }
        | ProgramStatement::StepValue {
            expression: condition,
            ..
        } => visit(condition),
        ProgramStatement::Store { pointer, value }
        | ProgramStatement::TypedStore { pointer, value, .. } => {
            visit(pointer);
            visit(value);
        }
        ProgramStatement::CopyAggregate { target, source, .. }
        | ProgramStatement::InitializeScalarArray { target, source, .. } => {
            visit(target);
            visit(source);
        }
        ProgramStatement::Update {
            target, operand, ..
        } => {
            visit(target);
            visit(operand);
        }
        ProgramStatement::ForStep { step, .. } => statement_function_addresses(step, taken),
        ProgramStatement::Seq(statements) => {
            charge_seq_spine(statements);
            for statement in statements.iter() {
                statement_function_addresses(statement, taken);
            }
        }
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            statement_function_addresses(try_body, taken);
            statement_function_addresses(handler, taken);
        }
        ProgramStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            visit(condition);
            statement_function_addresses(then_branch, taken);
            statement_function_addresses(else_branch, taken);
        }
        ProgramStatement::While {
            condition, body, ..
        } => {
            visit(condition);
            statement_function_addresses(body, taken);
        }
        ProgramStatement::Switch { expression, cases } => {
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
fn function_address_taken(function: &ProgramFunction, taken: &mut BTreeSet<String>) {
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
        .flat_map(|array| array.initial_values.values())
        .chain(
            function
                .static_arrays()
                .iter()
                .flat_map(|array| array.initial_values.values()),
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
    BTreeMap<String, &'a ProgramFunction>,
    BTreeMap<String, BTreeSet<String>>,
);

fn termination_call_graph<'a>(
    partial_rules: &'a [VerifiedFunctionRule],
    inline_bodies: &[&'a ProgramFunction],
) -> TerminationCallGraph<'a> {
    let mut functions = partial_rules
        .iter()
        .map(|rule| (rule.function.name.clone(), &rule.function))
        .collect::<BTreeMap<_, _>>();
    // A user-defined tactic's procedure runs no code, so its body has no
    // calls; the tactics its certified proof applied are its call edges.
    let applied_tactics = partial_rules
        .iter()
        .filter(|rule| !rule.applied_tactics.is_empty())
        .map(|rule| (rule.function.name.clone(), &rule.applied_tactics))
        .collect::<BTreeMap<_, _>>();
    charge_termination_work(partial_rules.len() + inline_bodies.len());
    let unruled_bodies = inline_bodies
        .iter()
        .filter(|function| !functions.contains_key(function.name()))
        .map(|function| (function.name().to_string(), *function))
        .collect::<BTreeMap<_, _>>();
    let checked_calls = partial_rules
        .iter()
        .map(|rule| (rule.function.name(), rule.checked_callees.as_ref()))
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
        let mut found = match checked_calls.get(function.name()) {
            Some(Some(callees)) => {
                charge_termination_work(callees.len());
                classify_termination_callees(function, callees.iter().cloned())
            }
            Some(None) | None => termination_callees(function),
        };
        if let Some(tactics) = applied_tactics.get(&name) {
            charge_termination_work(tactics.len());
            found.extend(tactics.iter().cloned());
        }
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
///   [`crate::kernel::program_execution_environment_with_recursion_anchor`] reads
///   to build the anchor, and the certified [`ProgramFunction`] here is the one the
///   rule was issued for, so a measure present here is a measure that was
///   anchored. A plan claiming a measure the interface does not carry is a
///   plan for obligations nobody emitted, and it is refused.
/// * every recursive edge of this function is a self-call or a call to a
///   member its own interface names as a recursion peer, and that member
///   declares an expression measure too. The anchor is read off the same
///   interface, so a call to a named peer owed the peer's measure below this
///   function's entry reading; a call to an unnamed member would owe
///   nothing, and a cycle through it would be certified with no descent, so
///   it is refused by name. Every member of a component is checked this
///   way, so every edge of the cycle was ranked, each in the one
///   lexicographic order all the members' measures share.
/// * every loop a recursive call sits inside was certified under this function's
///   anchor. A loop is verified once as its own judgment and then applied as
///   a summary, so a call the summary swallowed owes nothing at the step that
///   applies it; what makes it owe the descent is that the loop's own body
///   was stepped under the anchor. The certified [`VerifiedLoopRule`] records
///   which anchor that was — the kernel writes it from the environment the
///   paths were produced in, and the surface has no way to set it — so this
///   reads the rule, never the plan, which names only a spelling.
///
/// Work is the component's own members and this function's own statement
/// tree; nothing ambient is scanned.
fn check_expression_measure_recursion(
    name: &str,
    source: &str,
    function: &ProgramFunction,
    recursive_callees: &BTreeSet<String>,
    plans: &BTreeMap<String, FunctionTerminationPlan>,
    loop_rules: &[VerifiedLoopRule],
) -> Result<(), TerminationError> {
    if !function.contract_interface().has_call_ranked_recursion() {
        return Err(error(format!(
            "the termination plan ranks `{name}` by the expression measure `{source}`, but the \
             certified `{name}` carries no declared measure, so no recursive call of it owed a \
             descent obligation"
        )));
    }
    let peers = function.contract_interface().recursion_peers();
    for callee in recursive_callees {
        charge_termination_work(1);
        if callee == name {
            continue;
        }
        if peers
            .binary_search_by(|peer| peer.as_str().cmp(callee))
            .is_err()
        {
            return Err(error(format!(
                "`{name}` declares the expression `decreases` measure `{source}` and is in a \
                 recursive component with `{callee}`, but its certified interface does not name \
                 `{callee}` as a recursion peer, so a call to `{callee}` would be ranked by \
                 nothing"
            )));
        }
    }
    // Every member of a settled component agrees on its measure kind.
    for member in std::iter::once(name).chain(recursive_callees.iter().map(String::as_str)) {
        charge_termination_work(1);
        if !matches!(
            plans
                .get(member)
                .and_then(|plan| plan.recursive_measure.as_ref()),
            Some(FunctionTerminationMeasure::Expression(_))
        ) {
            return Err(error(
                "a recursive component cannot mix an expression measure with another measure kind",
            ));
        }
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
    let mut next_index = 0;
    let mut enclosing = Vec::new();
    let mut self_call_loops = BTreeSet::new();
    self_call_loop_indices(
        &function.source_body,
        recursive_callees,
        &mut next_index,
        &mut enclosing,
        &mut self_call_loops,
    );
    let loops = loops_in_order(&function.source_body);
    for index in self_call_loops {
        charge_termination_work(1);
        // The rule is bound to this source loop the way
        // `verified_loop_ranking_measures` binds one: by index and executable
        // shape. Reading the shape here too keeps this check standing on its
        // own rather than on that later pass's ordering. The loops are
        // listed once, so each index is a lookup.
        let source_loop = loops.get(index).copied();
        let anchored = loop_rules.iter().any(|rule| {
            rule.loop_index == Some(index)
                && rule
                    .recursion_anchor
                    .as_ref()
                    .is_some_and(|anchor| anchor.ranks(name, function.contract_interface()))
                && source_loop.is_some_and(|source_loop| {
                    same_statement_shape(source_loop, &rule.loop_statement)
                })
        });
        if !anchored {
            return Err(error(format!(
                "`{name}` declares the expression `decreases` measure `{source}` and makes a \
                 recursive call inside loop {index}, whose verified rule was certified without `{name}`'s \
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
pub(super) fn statement_calls_function(statement: &ProgramStatement, callee: &str) -> bool {
    charge_termination_work(1);
    let both = |left: &ProgramStatement, right: &ProgramStatement| {
        statement_calls_function(left, callee) || statement_calls_function(right, callee)
    };
    match statement {
        ProgramStatement::Call { function_name, .. }
        | ProgramStatement::CallResult { function_name, .. }
        | ProgramStatement::CallConstruct { function_name, .. } => function_name == callee,
        ProgramStatement::While { body, .. } => statement_calls_function(body, callee),
        ProgramStatement::Seq(statements) => both(statements.first(), &statements.rest()),
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => both(then_branch, else_branch),
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        } => both(try_body, handler),
        ProgramStatement::Switch { cases, .. } => cases
            .iter()
            .any(|case| statement_calls_function(&case.body, callee)),
        ProgramStatement::ForStep { step, .. } => statement_calls_function(step, callee),
        ProgramStatement::Skip
        | ProgramStatement::EndScalarReference(_)
        | ProgramStatement::ScalarReferenceScope(_)
        | ProgramStatement::EndAutomaticLifetimes { .. }
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::Declare { .. }
        | ProgramStatement::DeclareAggregate { .. }
        | ProgramStatement::Assign { .. }
        | ProgramStatement::HeapAllocate { .. }
        | ProgramStatement::HeapFree { .. }
        | ProgramStatement::Assert { .. }
        | ProgramStatement::StepValue { .. }
        | ProgramStatement::LoopTest { .. }
        | ProgramStatement::Throw(_)
        | ProgramStatement::Return(_)
        | ProgramStatement::Store { .. }
        | ProgramStatement::TypedStore { .. }
        | ProgramStatement::CopyAggregate { .. }
        | ProgramStatement::InitializeScalarArray { .. }
        | ProgramStatement::Update { .. } => false,
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
    statement: &ProgramStatement,
    callee: &BTreeSet<String>,
    next_index: &mut usize,
    enclosing: &mut Vec<usize>,
    found: &mut BTreeSet<usize>,
) {
    charge_termination_work(1);
    let mut descend = |statement: &ProgramStatement, next_index: &mut usize| {
        self_call_loop_indices(statement, callee, next_index, enclosing, found);
    };
    match statement {
        ProgramStatement::Call { function_name, .. }
        | ProgramStatement::CallResult { function_name, .. }
        | ProgramStatement::CallConstruct { function_name, .. } => {
            if callee.contains(function_name) {
                found.extend(enclosing.iter().copied());
            }
        }
        ProgramStatement::While { body, .. } => {
            let index = *next_index;
            *next_index += 1;
            enclosing.push(index);
            self_call_loop_indices(body, callee, next_index, enclosing, found);
            enclosing.pop();
        }
        ProgramStatement::Seq(statements) => {
            charge_seq_spine(statements);
            for statement in statements.iter() {
                descend(statement, next_index);
            }
        }
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            descend(then_branch, next_index);
            descend(else_branch, next_index);
        }
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            descend(try_body, next_index);
            descend(handler, next_index);
        }
        ProgramStatement::Switch { cases, .. } => {
            for case in cases {
                descend(&case.body, next_index);
            }
        }
        ProgramStatement::ForStep { step, .. } => descend(step, next_index),
        // Spelled out, as in `loop_at_index` and `check_loops`: these walks
        // number the same loops only while they descend into the same
        // statements, so a new statement kind must be placed in all of them.
        ProgramStatement::Skip
        | ProgramStatement::EndScalarReference(_)
        | ProgramStatement::ScalarReferenceScope(_)
        | ProgramStatement::EndAutomaticLifetimes { .. }
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::Declare { .. }
        | ProgramStatement::DeclareAggregate { .. }
        | ProgramStatement::Assign { .. }
        | ProgramStatement::HeapAllocate { .. }
        | ProgramStatement::HeapFree { .. }
        | ProgramStatement::Assert { .. }
        | ProgramStatement::StepValue { .. }
        | ProgramStatement::LoopTest { .. }
        | ProgramStatement::Throw(_)
        | ProgramStatement::Return(_)
        | ProgramStatement::Store { .. }
        | ProgramStatement::TypedStore { .. }
        | ProgramStatement::CopyAggregate { .. }
        | ProgramStatement::InitializeScalarArray { .. }
        | ProgramStatement::Update { .. } => {}
    }
}

/// Proposes a height for every node of the termination call graph: zero for a
/// function that calls no other node, and otherwise one more than its highest
/// callee outside its own recursive cycle. The members of a cycle share a
/// height.
///
/// The result is untrusted. [`program_verified_function_termination_rules`] checks
/// at every call site that the callee is not above its caller, and treats
/// every call between equal heights as a recursive edge that a declared
/// measure must rank, so a wrong height can only refuse a function or fail
/// the check; it cannot certify one. This is Tarjan's algorithm with an
/// explicit stack, so a call chain as deep as the project is long costs heap
/// and not machine stack. Work is linear in the nodes and their call edges.
pub fn program_termination_height_plan(
    partial_rules: &[VerifiedFunctionRule],
    inline_bodies: &[&ProgramFunction],
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
pub enum TerminationRefusal {
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

impl std::fmt::Display for TerminationRefusal {
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
pub struct UnsuitableCallback {
    pub taker: String,
    pub callback: String,
}

/// The outcome of one termination check: evidence for the functions shown to
/// return, and one reason for each function that was not.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TerminationVerdicts {
    pub rules: Vec<VerifiedFunctionTerminationRule>,
    pub refusals: BTreeMap<String, TerminationRefusal>,
    /// Functions declared diverging that this check would otherwise have
    /// certified: every loop ranked and every call descending. They receive
    /// no evidence, and the caller of this check decides what an unjustified
    /// declaration means.
    pub unjustified_diverging: Vec<String>,
    /// Address-takings that keep every call through a function pointer
    /// refused. While this is nonempty the verdicts are the strict ones, and
    /// `refusals` says why each named callback does not qualify.
    pub unsuitable_callbacks: Vec<UnsuitableCallback>,
}

/// Checks untrusted ranking plans against exact partially-correct function
/// rules and returns the independently usable subset proved to terminate.
///
/// The judgment is local descent. `heights` is an untrusted proposal, as
/// [`program_termination_height_plan`] makes one: every call must reach a callee
/// that is not above its caller, a strictly lower callee must already have
/// evidence, and a callee at the caller's own height is a recursive edge that
/// the caller's declared measure must rank. Soundness is one induction on the
/// pair of height and measure, so nothing here searches the call graph: each
/// function reads its own call sites and loops, and levels are settled in
/// ascending order with work linear in their recursive edges.
///
/// `assumed_terminating` names callees outside the verified set whose
/// declarations promise that they return: an external contract, or a function
/// this run did not select. They are knowns in the same sense as those
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
pub fn program_verified_function_termination_rules(
    partial_rules: &[VerifiedFunctionRule],
    plan_entries: &[FunctionTerminationPlan],
    verified_loop_rules: &BTreeMap<String, Vec<VerifiedLoopRule>>,
    inline_bodies: &[&ProgramFunction],
    heights: &BTreeMap<String, usize>,
    assumed_terminating: &BTreeSet<String>,
    declared_diverging: &BTreeSet<String>,
    diverging_contracts: &BTreeSet<String>,
) -> Result<TerminationVerdicts, TerminationError> {
    obligations::TerminationObligations::generate(
        partial_rules,
        plan_entries,
        verified_loop_rules,
        inline_bodies,
        heights,
        assumed_terminating,
        declared_diverging,
        diverging_contracts,
        false,
    )?
    .prove_implicitly()
}

#[cfg(test)]
mod address_escape_tests {
    use super::*;

    #[test]
    fn subobject_child_mentions_only_its_actual_source_variables() {
        let child = ProgramExpression::TypedLoad {
            pointer: Box::new(ProgramExpression::Subobject {
                pointer: Box::new(ProgramExpression::PointerOffsetBytes {
                    pointer: Box::new(ProgramExpression::Variable("p".into())),
                    bytes: 8,
                }),
                width: 8,
            }),
            value_type: ProgramType::Int32Pointer,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: ExpressionLoadSource::none(),
        };
        assert!(program_expression_mentions_variable(&child, "p"));
        for name in ["identity", "value", "left_model", "right_model"] {
            assert!(!program_expression_mentions_variable(&child, name));
        }
    }

    use std::sync::Arc;

    fn variable(name: &str) -> ProgramExpression {
        ProgramExpression::Variable(name.to_string())
    }

    fn address_of(name: &str) -> ProgramExpression {
        ProgramExpression::AddressOf(Box::new(variable(name)))
    }

    #[test]
    fn store_through_escaped_address_is_detected() {
        // p = &i; *p = q;
        let escape = ProgramStatement::Assign {
            source: Default::default(),
            name: "p".to_string(),
            expression: address_of("i"),
            prior_result: None,
        };
        let store = ProgramStatement::Store {
            pointer: variable("p"),
            value: variable("q"),
        };
        let body = ProgramStatement::seq(Arc::new(escape), Arc::new(store));
        assert!(address_taken_locals(&body).contains("i"));
        assert!(!address_taken_locals(&body).contains("q"));
        assert!(reject_address_escaped_measure("spin", "i", &address_taken_locals(&body)).is_err());
        assert!(reject_address_escaped_measure("spin", "q", &address_taken_locals(&body)).is_ok());
    }

    #[test]
    fn helper_call_receiving_the_address_is_detected() {
        let call = ProgramStatement::Call {
            function_name: "reset".to_string(),
            arguments: vec![address_of("n")],
            callee: None,
        };
        assert!(address_taken_locals(&call).contains("n"));
        assert!(reject_address_escaped_measure("f", "n", &address_taken_locals(&call)).is_err());
    }

    #[test]
    fn escape_inside_a_loop_or_branch_body_is_detected() {
        let escape = ProgramStatement::Assign {
            source: Default::default(),
            name: "p".to_string(),
            expression: ProgramExpression::Add(Box::new(address_of("n")), Box::new(variable("k"))),
            prior_result: None,
        };
        let branch = ProgramStatement::If {
            condition: variable("c"),
            then_branch: Box::new(ProgramStatement::Skip),
            else_branch: Box::new(escape),
        };
        let body = ProgramStatement::While {
            ranking_measures: Vec::new(),
            structural_measure: None,
            condition: variable("c"),
            invariant: Vec::new(),
            invariant_checks: Vec::new(),
            effect_checks: Vec::new(),
            resource_specs: Vec::new(),
            do_while: false,
            backedge_target: None,
            natural_exit_target: None,
            body: Box::new(branch),
        };
        assert!(address_taken_locals(&body).contains("n"));
        assert!(!address_taken_locals(&body).contains("c"));
    }
}

#[cfg(test)]
mod ranking_member_tests {
    use super::*;

    fn scalar_state(bindings: &[(&str, MachineTerm)]) -> ExecutionState {
        let mut state = ExecutionState::new();
        for (name, value) in bindings {
            state.locals.set_typed(
                (*name).to_string(),
                ProgramValue::Int32(value.clone()),
                ProgramType::Int32,
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
        let state = scalar_state(&[("i", MachineTerm::Variable(Variable(1)))]);
        let volatile_read = ProgramExpression::TypedLoad {
            pointer: Box::new(ProgramExpression::Variable("device".to_string())),
            value_type: ProgramType::Int32,
            volatile: true,
            pointee_constant: false,
            access_class: None,
            source: ExpressionLoadSource::none(),
        };
        let measures = vec![RankingComponent::ProgramExpression(
            ProgramExpression::Subtract(
                Box::new(volatile_read),
                Box::new(ProgramExpression::Variable("i".to_string())),
            ),
        )];
        let error = collect_loop_ranking_obligations(
            &state,
            &state,
            None,
            &measures,
            &PureFactContext::default(),
            &mut ExecutionBudget::default(),
        )
        .expect_err("a volatile read has no value at a state");
        assert!(error.contains("volatile"), "{error}");
    }

    #[test]
    fn ranking_members_are_ordered_and_right_nested() {
        let outer = MachineTerm::Variable(Variable(1));
        let inner = MachineTerm::Variable(Variable(2));
        let entry = scalar_state(&[("i", outer.clone()), ("j", inner.clone())]);
        let post_outer = MachineTerm::subtract(outer.clone(), MachineTerm::constant(1));
        let post_inner = MachineTerm::add(inner.clone(), MachineTerm::constant(1));
        let back_edge = scalar_state(&[("i", post_outer.clone()), ("j", post_inner.clone())]);
        let measures = vec![
            RankingComponent::ProgramExpression(ProgramExpression::Variable("i".to_string())),
            RankingComponent::ProgramExpression(ProgramExpression::Variable("j".to_string())),
        ];
        let obligations = collect_loop_ranking_obligations(
            &back_edge,
            &entry,
            None,
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
                    ConditionTerm::signed_less_equal(MachineTerm::constant(0), post),
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
        let value = MachineTerm::Variable(Variable(7));
        let entry = scalar_state(&[("n", value.clone())]);
        let post = MachineTerm::subtract(value.clone(), MachineTerm::constant(1));
        let back_edge = scalar_state(&[("n", post.clone())]);
        let measures = vec![RankingComponent::ProgramExpression(
            ProgramExpression::Variable("n".to_string()),
        )];
        let obligations = collect_loop_ranking_obligations(
            &back_edge,
            &entry,
            None,
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
            pointer: Box::new(SpecExpression::Value(ProgramValue::Pointer(
                PointerValue::new(cell.clone(), ProgramType::Int32Pointer),
            ))),
            value_type: ProgramType::Int32,
        }
    }

    /// The surface hands the kernel ONE pure component, and the kernel is what
    /// picks the two states to read it at. Nothing in the declaration names a
    /// state, so the entry and back-edge sides of the decrease member are the
    /// values that one expression takes at the two states it is read at.
    #[test]
    fn a_pure_component_is_read_at_both_states() {
        let cell = int32_cell("counter");
        let value = MachineTerm::Variable(Variable(11));
        let post = MachineTerm::subtract(value.clone(), MachineTerm::constant(1));
        let mut entry = ExecutionState::new();
        entry.memory = Memory::new().store(cell.clone(), ProgramValue::Int32(value.clone()));
        let mut back_edge = ExecutionState::new();
        back_edge.memory = Memory::new().store(cell.clone(), ProgramValue::Int32(post.clone()));
        let measures = vec![RankingComponent::Pure {
            source: "count(counter)".to_string(),
            expression: current_load(&cell),
        }];

        let obligations = collect_loop_ranking_obligations(
            &back_edge,
            &entry,
            None,
            &measures,
            &PureFactContext::default(),
            &mut ExecutionBudget::default(),
        )
        .expect("a pure measure reads at both ends");

        assert_eq!(obligations.len(), 2);
        // Each member reads a stored cell, which names its version; compare
        // through the read-over-write authority.
        let resolved = |proposition: &Proposition| {
            crate::kernel::eval::comparison_form(proposition).unwrap_or_else(|| proposition.clone())
        };
        assert_eq!(
            resolved(obligations[0].proposition()),
            Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(MachineTerm::constant(0), post.clone()),
                true,
            ),
            "the nonnegativity member reads the back-edge state"
        );
        assert_eq!(
            resolved(obligations[1].proposition()),
            Proposition::ConditionIs(ConditionTerm::signed_less_than(post, value), true),
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

    fn current_integer_local(name: &str) -> SpecIntegerExpression {
        SpecIntegerExpression::FromMachine(Box::new(SpecExpression::ProgramExpression(
            ProgramExpression::Variable(name.to_string()),
        )))
    }

    fn observed_word(value: MachineTerm) -> SharedIntegerTerm {
        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            value,
        ))
        .into()
    }

    /// An `Integer`-valued component owes the same two members, `0 <= m` and
    /// `m_post < m_pre`, built from the two readings of the one declared
    /// component. An observation of one machine value compared with a
    /// constant or another observation of its type retains that machine
    /// carrier in an Integer comparison.
    #[test]
    fn an_integer_component_builds_integer_members() {
        let value = MachineTerm::Variable(Variable(13));
        let post = MachineTerm::subtract(value.clone(), MachineTerm::constant(1));
        let entry = scalar_state(&[("n", value.clone())]);
        let back_edge = scalar_state(&[("n", post.clone())]);
        let measures = vec![RankingComponent::PureInteger {
            source: "level(n)".to_string(),
            expression: current_integer_local("n"),
        }];

        let obligations = collect_loop_ranking_obligations(
            &back_edge,
            &entry,
            None,
            &measures,
            &PureFactContext::default(),
            &mut ExecutionBudget::default(),
        )
        .expect("an Integer measure reads at both ends");

        assert_eq!(obligations.len(), 2);
        assert_eq!(
            obligations[0].proposition(),
            &Proposition::ConditionIs(
                ConditionTerm::IntegerLessEqual(
                    observed_word(MachineTerm::constant(0)),
                    observed_word(post.clone())
                ),
                true,
            ),
            "the nonnegativity member is the retained comparison at the back edge"
        );
        assert_eq!(
            obligations[1].proposition(),
            &Proposition::ConditionIs(
                ConditionTerm::IntegerLessThan(
                    observed_word(post.clone()),
                    observed_word(value.clone())
                ),
                true,
            ),
            "the decrease member is the retained comparison against the iteration entry"
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
    /// own carrier and no comparison crosses them; an Integer member over one
    /// int32 observation retains that carrier in an Integer comparison.
    #[test]
    fn a_mixed_tuple_builds_each_member_in_its_own_carrier() {
        let outer = MachineTerm::Variable(Variable(17));
        let inner = MachineTerm::Variable(Variable(19));
        let post_outer = MachineTerm::subtract(outer.clone(), MachineTerm::constant(1));
        let post_inner = MachineTerm::subtract(inner.clone(), MachineTerm::constant(1));
        let entry = scalar_state(&[("i", outer.clone()), ("n", inner.clone())]);
        let back_edge = scalar_state(&[("i", post_outer.clone()), ("n", post_inner.clone())]);
        let measures = vec![
            RankingComponent::ProgramExpression(ProgramExpression::Variable("i".to_string())),
            RankingComponent::PureInteger {
                source: "level(n)".to_string(),
                expression: current_integer_local("n"),
            },
        ];

        let obligations = collect_loop_ranking_obligations(
            &back_edge,
            &entry,
            None,
            &measures,
            &PureFactContext::default(),
            &mut ExecutionBudget::default(),
        )
        .expect("a mixed tuple reads each component in its own carrier");

        assert_eq!(obligations.len(), 3);
        assert_eq!(
            obligations[0].proposition(),
            &Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(MachineTerm::constant(0), post_outer.clone()),
                true,
            )
        );
        assert_eq!(
            obligations[1].proposition(),
            &Proposition::ConditionIs(
                ConditionTerm::IntegerLessEqual(
                    observed_word(MachineTerm::constant(0)),
                    observed_word(post_inner.clone())
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
                ConditionTerm::IntegerLessThan(observed_word(post_inner), observed_word(inner)),
                true,
            )),
        );
        assert_eq!(
            obligations[2].proposition(),
            &Proposition::Or(Box::new(pivot_first), Box::new(pivot_second)),
            "each pivot compares its own component's two readings"
        );
    }

    /// Logical ranking values impose only their ranking obligations.
    #[test]
    fn a_pure_component_does_not_publish_read_validity() {
        let cell = int32_cell("counter");
        let entry = ExecutionState::new();
        let back_edge = ExecutionState::new();
        let measures = vec![RankingComponent::Pure {
            source: "count(counter)".to_string(),
            expression: current_load(&cell),
        }];

        let obligations = collect_loop_ranking_obligations(
            &back_edge,
            &entry,
            None,
            &measures,
            &PureFactContext::default(),
            &mut ExecutionBudget::default(),
        )
        .expect("an unknown cell still has a symbolic value");

        let loadable = obligations
            .iter()
            .filter(|obligation| {
                matches!(obligation.proposition(), Proposition::MemoryLoadable { .. })
            })
            .count();
        assert_eq!(loadable, 0, "logical ranking terms grant no validity");
        assert_eq!(
            obligations.len(),
            2,
            "nonnegativity and strict decrease remain required"
        );
    }

    fn typed_state(name: &str, value: ProgramValue, program_type: ProgramType) -> ExecutionState {
        let mut state = ExecutionState::new();
        state
            .locals
            .set_typed(name.to_string(), value, program_type);
        state
    }

    fn ranking_members(
        back_edge: &ExecutionState,
        entry: &ExecutionState,
        measure: ProgramExpression,
    ) -> Result<Vec<Proposition>, String> {
        collect_loop_ranking_obligations(
            back_edge,
            entry,
            None,
            &[RankingComponent::ProgramExpression(measure)],
            &PureFactContext::default(),
            &mut ExecutionBudget::default(),
        )
        .map(|obligations| {
            obligations
                .iter()
                .map(|obligation| obligation.proposition().clone())
                .collect()
        })
    }

    fn uint32_state(value: MachineTerm) -> ExecutionState {
        typed_state("x", ProgramValue::UInt32(value), ProgramType::UInt32)
    }

    fn four_minus_x() -> ProgramExpression {
        ProgramExpression::Subtract(
            Box::new(ProgramExpression::Value(ProgramValue::Int32(
                MachineTerm::constant(4),
            ))),
            Box::new(ProgramExpression::Variable("x".to_string())),
        )
    }

    /// `4 - x` over a `uint32 x` is a uint32 expression under C's usual
    /// arithmetic conversions, so it ranks by unsigned order: its
    /// nonnegativity member is `true` and its decrease member is the unsigned
    /// comparison of the two wrapped differences.
    #[test]
    fn an_unsigned_component_ranks_by_unsigned_order() {
        let value = MachineTerm::Variable(Variable(21));
        let entry = uint32_state(value.clone());
        let back_edge = uint32_state(MachineTerm::add(value.clone(), MachineTerm::constant(1)));
        let members = ranking_members(&back_edge, &entry, four_minus_x())
            .expect("a uint32 measure reads at both ends");
        assert_eq!(
            members,
            vec![
                Proposition::ConditionIs(ConditionTerm::Constant(true), true),
                Proposition::ConditionIs(
                    ConditionTerm::unsigned_less_than(
                        canonical_ranking_term(&MachineTerm::subtract(
                            MachineTerm::constant(3),
                            value.clone(),
                        )),
                        canonical_ranking_term(&MachineTerm::subtract(
                            MachineTerm::constant(4),
                            value,
                        )),
                    ),
                    true,
                ),
            ]
        );
    }

    /// The decrease member compares the values C computes, wraparound
    /// included. At concrete states it is decided outright: `x` from 0 to 1
    /// moves `4 - x` from 4 to 3, a descent, while `x` from 4 to 5 moves it
    /// from 0 to 2^32 - 1, which wraps upward and is refused even though the
    /// mathematical difference fell.
    #[test]
    fn an_unsigned_component_that_wraps_upward_does_not_descend() {
        let decrease = |before: u32, after: u32| {
            ranking_members(
                &uint32_state(MachineTerm::constant(after)),
                &uint32_state(MachineTerm::constant(before)),
                four_minus_x(),
            )
            .expect("a uint32 measure reads at both ends")
            .pop()
            .expect("a decrease member")
        };
        assert_eq!(
            decrease(0, 1),
            Proposition::ConditionIs(ConditionTerm::Constant(true), true)
        );
        assert_eq!(
            decrease(4, 5),
            Proposition::ConditionIs(ConditionTerm::Constant(false), true)
        );
    }

    /// A uint64 measure ranks by unsigned sixty-four-bit order, and its
    /// wraparound below zero is a growth, not a descent.
    #[test]
    fn a_uint64_component_ranks_by_unsigned_order() {
        let state = |value: u64| {
            typed_state(
                "x",
                ProgramValue::UInt64(MachineTerm::uint64_constant(value)),
                ProgramType::UInt64,
            )
        };
        let x = || ProgramExpression::Variable("x".to_string());
        let down = ranking_members(&state(4), &state(5), x()).expect("uint64 measure");
        assert_eq!(
            down,
            vec![
                Proposition::ConditionIs(ConditionTerm::Constant(true), true),
                Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            ]
        );
        let wrapped = ranking_members(&state(u64::MAX), &state(0), x()).expect("uint64 measure");
        assert_eq!(
            wrapped[1],
            Proposition::ConditionIs(ConditionTerm::Constant(false), true)
        );
    }

    /// A `uint8` operand is promoted to `int`, as C promotes it, so a measure
    /// over a `uint8` counter is an int32 measure over the counter's `int32`
    /// widening and owes the signed members.
    #[test]
    fn a_narrow_unsigned_component_is_promoted_to_int32() {
        let value = MachineTerm::Variable(Variable(22));
        let state = typed_state("x", ProgramValue::UInt8(value.clone()), ProgramType::UInt8);
        let members = ranking_members(&state, &state, ProgramExpression::Variable("x".to_string()))
            .expect("a uint8 measure reads at both ends");
        assert_eq!(
            members[0],
            Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(
                    MachineTerm::constant(0),
                    MachineTerm::machine_integer_cast(
                        MachineIntegerType::UInt8,
                        MachineIntegerType::Int32,
                        value
                    ),
                ),
                true,
            )
        );
    }

    /// A pure component whose value is a `uint32` takes the unsigned carrier
    /// too, so a measure the spec evaluator reads ranks exactly as the same
    /// value read from a C expression does.
    #[test]
    fn a_pure_uint32_component_ranks_by_unsigned_order() {
        let value = MachineTerm::Variable(Variable(23));
        let state = ExecutionState::new();
        let obligations = collect_loop_ranking_obligations(
            &state,
            &state,
            None,
            &[RankingComponent::Pure {
                source: "x".to_string(),
                expression: SpecExpression::Value(ProgramValue::UInt32(value.clone())),
            }],
            &PureFactContext::default(),
            &mut ExecutionBudget::default(),
        )
        .expect("a pure uint32 value reads at both ends");
        assert_eq!(
            obligations[0].proposition(),
            &Proposition::ConditionIs(ConditionTerm::Constant(true), true)
        );
        assert_eq!(
            obligations[1].proposition(),
            &Proposition::ConditionIs(
                ConditionTerm::unsigned_less_than(value.clone(), value),
                true
            )
        );
    }

    /// An `int64` component ranks by signed 64-bit order and owes its lower
    /// bound, as an int32 one does: a negative reading fails the `0 <= m`
    /// member, and a reading that grows fails the decrease.
    #[test]
    fn an_int64_component_ranks_by_signed_order_and_owes_its_lower_bound() {
        let state = |value: i64| {
            typed_state(
                "x",
                ProgramValue::Int64(MachineTerm::int64_constant(value)),
                ProgramType::Int64,
            )
        };
        let x = || ProgramExpression::Variable("x".to_string());
        let holds = |value| Proposition::ConditionIs(ConditionTerm::Constant(value), true);
        let down = ranking_members(&state(4), &state(5), x()).expect("int64 measure");
        assert_eq!(down, vec![holds(true), holds(true)]);
        let negative = ranking_members(&state(-1), &state(5), x()).expect("int64 measure");
        assert_eq!(negative, vec![holds(false), holds(true)]);
        let up = ranking_members(&state(6), &state(5), x()).expect("int64 measure");
        assert_eq!(up[1], holds(false));
        // Below zero the unsigned reading of the same bits would be huge;
        // the signed one is what is compared.
        let past_zero = ranking_members(&state(-1), &state(0), x()).expect("int64 measure");
        assert_eq!(past_zero, vec![holds(false), holds(true)]);
    }

    /// The structural-path helper has no proof site to emit an undischarged
    /// obligation to, so it settles one only by an exact route. A disjunction
    /// with one available arm is exactly the shape the deleted general prover
    /// used to accept here by selecting the arm.
    #[test]
    fn structural_path_refuses_an_obligation_no_exact_route_settles() {
        let left = Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(
                MachineTerm::constant(0),
                MachineTerm::Variable(Variable(1)),
            ),
            true,
        );
        let right = Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(
                MachineTerm::constant(0),
                MachineTerm::Variable(Variable(2)),
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
    fn summarized_loop(condition: u32) -> ProgramStatement {
        crate::kernel::program_while(
            crate::kernel::program_expression::int32_literal(condition),
            vec![Proposition::ConditionIs(
                ConditionTerm::Constant(true),
                true,
            )],
            ProgramStatement::Skip,
        )
    }

    /// A verified rule whose body calls `callees` in order and then holds the
    /// given loops, which is all the termination check reads of a function.
    fn rule(name: &str, callees: &[&str], loops: usize) -> VerifiedFunctionRule {
        let mut body = ProgramStatement::Skip;
        for callee in callees {
            body = ProgramStatement::seq(
                Arc::new(body),
                Arc::new(crate::kernel::program_call(*callee, Vec::new())),
            );
        }
        for _ in 0..loops {
            body = ProgramStatement::seq(Arc::new(body), Arc::new(summarized_loop(1)));
        }
        VerifiedFunctionRule {
            pointer_result: None,
            function: ProgramFunction::new(ProgramType::Void, name, Vec::new(), body),
            loop_semantics: LoopSemantics::ApplyVerifiedRules,
            checked_callees: None,
            applied_tactics: Default::default(),
        }
    }

    fn check(
        rules: &[VerifiedFunctionRule],
        plans: &[FunctionTerminationPlan],
        heights: &BTreeMap<String, usize>,
        assumed: &[&str],
    ) -> Result<TerminationVerdicts, TerminationError> {
        program_verified_function_termination_rules(
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

    fn terminating(verdicts: &TerminationVerdicts) -> BTreeSet<&str> {
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
            program_termination_height_plan(&rules, &[]),
            heights(&[
                ("leaf", 0),
                ("middle", 1),
                ("ping", 1),
                ("pong", 1),
                ("top", 2)
            ])
        );
    }

    /// Heights are untrusted: one that inverts a call is an error, never
    /// evidence.
    #[test]
    fn a_callee_planned_above_its_caller_is_rejected() {
        let rules = [rule("caller", &["callee"], 0), rule("callee", &[], 0)];
        let forged = heights(&[("caller", 0), ("callee", 1)]);
        let error = check(&rules, &[], &forged, &[]).expect_err("an inverted plan must not check");
        assert!(error.message.contains("above its caller"), "{error}");
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
            TerminationRefusal::UnmeasuredRecursion {
                callee: "callee".to_string()
            }
        );
    }

    #[test]
    fn a_missing_height_is_rejected() {
        let rules = [rule("only", &[], 0)];
        let error =
            check(&rules, &[], &BTreeMap::new(), &[]).expect_err("every node needs a height");
        assert!(error.message.contains("assigns no height"), "{error}");
    }

    #[test]
    fn an_unmeasured_cycle_refuses_its_members_and_their_callers() {
        let rules = [
            rule("top", &["ping"], 0),
            rule("ping", &["pong"], 0),
            rule("pong", &["ping"], 0),
            rule("bystander", &[], 0),
        ];
        let plan = program_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert_eq!(terminating(&verdicts), BTreeSet::from(["bystander"]));
        assert!(matches!(
            verdicts.refusals["ping"],
            TerminationRefusal::UnmeasuredRecursion { .. }
        ));
        assert_eq!(
            verdicts.refusals["top"],
            TerminationRefusal::Callee {
                callee: "ping".to_string()
            }
        );
    }

    #[test]
    fn a_callee_outside_the_run_terminates_only_when_assumed() {
        let rules = [rule("caller", &["outside"], 0)];
        let plan = program_termination_height_plan(&rules, &[]);
        let refused = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert_eq!(
            refused.refusals["caller"],
            TerminationRefusal::Callee {
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
        let plan = program_termination_height_plan(&rules, &[]);
        let verdicts = program_verified_function_termination_rules(
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
            TerminationRefusal::UnrankedLoop { index: 0 }
        );
        assert_eq!(verdicts.unjustified_diverging, ["idle".to_string()]);
        assert_eq!(
            verdicts.refusals["caller"],
            TerminationRefusal::Callee {
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
            let mut body = crate::kernel::program_if(
                crate::kernel::program_expression::greater_than(
                    crate::kernel::program_expression::variable("n"),
                    crate::kernel::program_expression::int32_literal(0),
                ),
                crate::kernel::program_call(
                    callee,
                    vec![crate::kernel::program_expression::subtract(
                        crate::kernel::program_expression::variable("n"),
                        crate::kernel::program_expression::int32_literal(1),
                    )],
                ),
                ProgramStatement::Skip,
            );
            for _ in 0..loops {
                body = ProgramStatement::seq(Arc::new(body), Arc::new(summarized_loop(1)));
            }
            VerifiedFunctionRule {
                pointer_result: None,
                loop_semantics: LoopSemantics::ApplyVerifiedRules,
                checked_callees: None,
                applied_tactics: Default::default(),
                function: ProgramFunction::new(
                    ProgramType::Void,
                    name,
                    vec![crate::kernel::program_parameter("n", ProgramType::Int32)],
                    body,
                ),
            }
        };
        let measured = |name: &str| FunctionTerminationPlan {
            function_name: name.to_string(),
            recursive_measure: Some(FunctionTerminationMeasure::NumericParameter(0)),
            loop_measures: BTreeMap::new(),
        };
        // Both visiting orders: the refused member sorts first, then last.
        for (sound, spins) in [("ping", "a_spins"), ("ping", "z_spins")] {
            let rules = [countdown(sound, spins, 0), countdown(spins, sound, 1)];
            let plan = program_termination_height_plan(&rules, &[]);
            let verdicts = check(&rules, &[measured(sound), measured(spins)], &plan, &[])
                .expect("both recursive edges descend");
            assert!(terminating(&verdicts).is_empty(), "{verdicts:?}");
            assert_eq!(
                verdicts.refusals[spins],
                TerminationRefusal::UnrankedLoop { index: 0 }
            );
            assert_eq!(
                verdicts.refusals[sound],
                TerminationRefusal::Callee {
                    callee: spins.to_string()
                }
            );
        }
    }

    #[test]
    fn checked_frontier_measure_needs_no_plan_but_does_not_cover_other_loops() {
        let source_loop = crate::kernel::program_while(
            crate::kernel::program_expression::int32_literal(1),
            Vec::new(),
            ProgramStatement::Skip,
        );
        let body = ProgramStatement::seq(Arc::new(source_loop.clone()), Arc::new(source_loop));
        let ranking = |value| {
            LoopTerminationMeasure::Ranking(vec![RankingMeasureKey::ProgramExpression(
                crate::kernel::program_expression::int32_literal(value),
            )])
        };
        let certified = BTreeMap::from([(0, vec![ranking(1)])]);
        let mut next = 0;
        let mut unranked = Vec::new();
        check_loops(
            &body,
            &BTreeMap::new(),
            &certified,
            "f",
            &mut next,
            &mut unranked,
        )
        .unwrap();
        assert_eq!(next, 2);
        assert_eq!(unranked, [1]);
        let planned = BTreeMap::from([(0, ranking(2))]);
        assert!(check_loops(&body, &planned, &certified, "f", &mut 0, &mut Vec::new()).is_err());
        let planned = BTreeMap::from([(1, ranking(1))]);
        assert!(check_loops(&body, &planned, &certified, "f", &mut 0, &mut Vec::new()).is_err());
    }

    /// The loop lookup once had no arm for a try/catch, so it neither found a
    /// loop inside one nor counted past it, while `check_loops` numbers those
    /// loops. An index then named different source loops in the two walks.
    #[test]
    fn loop_lookup_numbers_loops_inside_try_catch_as_the_check_does() {
        let spin = |condition: u32| {
            crate::kernel::program_while(
                crate::kernel::program_expression::int32_literal(condition),
                Vec::new(),
                ProgramStatement::Skip,
            )
        };
        let body = ProgramStatement::seq(
            Arc::new(ProgramStatement::TryCatchInt32 {
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

        let loops = loops_in_order(&body);
        for (index, condition) in [(0, 1), (1, 2), (2, 3)] {
            let found = *loops
                .get(index)
                .unwrap_or_else(|| panic!("loop {index} exists"));
            assert!(
                same_statement_shape(found, &spin(condition)),
                "loop {index} must be the loop the check numbered {index}"
            );
        }
        assert!(loops.get(3).is_none());
    }

    /// A rule whose body calls `callees`, calls through the local object
    /// `through` when given one, and takes the address of each of `takes`.
    fn pointer_rule(
        name: &str,
        callees: &[&str],
        through: Option<&str>,
        takes: &[&str],
    ) -> VerifiedFunctionRule {
        let mut body = ProgramStatement::Skip;
        for callee in callees {
            body = ProgramStatement::seq(
                Arc::new(body),
                Arc::new(crate::kernel::program_call(*callee, Vec::new())),
            );
        }
        for taken in takes {
            body = ProgramStatement::seq(
                Arc::new(body),
                Arc::new(ProgramStatement::Assign {
                    source: Default::default(),
                    name: "slot".to_string(),
                    expression: crate::kernel::program_expression::function_address(*taken),
                    prior_result: None,
                }),
            );
        }
        let parameters = match through {
            Some(object) => {
                body = ProgramStatement::seq(
                    Arc::new(body),
                    Arc::new(crate::kernel::program_call(object, Vec::new())),
                );
                vec![crate::kernel::program_parameter(
                    object,
                    ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
                )]
            }
            None => Vec::new(),
        };
        VerifiedFunctionRule {
            pointer_result: None,
            function: ProgramFunction::new(ProgramType::Void, name, parameters, body),
            loop_semantics: LoopSemantics::ApplyVerifiedRules,
            checked_callees: None,
            applied_tactics: Default::default(),
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
        let plan = program_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert_eq!(
            terminating(&verdicts),
            BTreeSet::from(["caller", "compare", "sort"])
        );
        assert!(verdicts.unsuitable_callbacks.is_empty());
    }

    #[test]
    fn program_completion_requires_callback_safety_even_without_requested_returns() {
        let rules = [
            pointer_rule("spin", &["apply"], None, &["spin"]),
            pointer_rule("apply", &[], Some("callback"), &[]),
        ];
        let owner = ProgramContractProof::open(BTreeSet::new(), BTreeSet::new(), &BTreeSet::new());
        let result = owner
            .generate_termination(ProgramTerminationInputs {
                partial_rules: &rules,
                plans: &[],
                inline_bodies: &[],
                assumed_terminating: &BTreeSet::new(),
                diverging_contracts: &BTreeSet::new(),
                has_unselected_functions: false,
            })
            .and_then(|proof| proof.prove_implicitly());
        assert!(matches!(
            result,
            Err(ProgramContractFailure::Obligation {
                goal: ProgramContractGoal::CallbackSafety,
                ..
            })
        ));
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
        let plan = program_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert!(terminating(&verdicts).is_empty(), "{verdicts:?}");
        assert_eq!(
            verdicts.unsuitable_callbacks,
            [UnsuitableCallback {
                taker: "spin".to_string(),
                callback: "spin".to_string(),
            }]
        );
        assert_eq!(
            verdicts.refusals["apply"],
            TerminationRefusal::IndirectCall {
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
        let plan = program_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        // Taking an address is not a call, so `install` itself returns.
        assert_eq!(
            terminating(&verdicts),
            BTreeSet::from(["bystander", "install"])
        );
        assert_eq!(
            verdicts.unsuitable_callbacks,
            [UnsuitableCallback {
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
        let plan = program_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert!(terminating(&verdicts).is_empty(), "{verdicts:?}");
        assert_eq!(verdicts.unsuitable_callbacks.len(), 1);
        assert_eq!(
            verdicts.refusals["loops"],
            TerminationRefusal::UnrankedLoop { index: 0 }
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
        Arc::make_mut(&mut applies.function.contract_interface)
            .contract_requires
            .push(SpecProposition::Predicate {
                resource_state_dependent: true,
                name: FunctionContract::predicate_name_for("Spinner"),
                arguments: vec![SpecPredicateArgument::Value(
                    SpecExpression::ProgramExpression(ProgramExpression::Variable(
                        "callback".to_string(),
                    )),
                )],
            });
        let rules = [pointer_rule("caller", &["applies"], None, &[]), applies];
        let plan = program_termination_height_plan(&rules, &[]);
        let contracts = BTreeSet::from(["Spinner".to_string()]);

        // A contract with no marker leaves the pointer call authorized.
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert_eq!(
            terminating(&verdicts),
            BTreeSet::from(["applies", "caller"])
        );

        let verdicts = program_verified_function_termination_rules(
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
            TerminationRefusal::DivergingContract {
                object: "callback".to_string(),
                contract: "Spinner".to_string(),
            }
        );
        assert_eq!(
            verdicts.refusals["caller"],
            TerminationRefusal::Callee {
                callee: "applies".to_string()
            }
        );
        assert!(verdicts.unjustified_diverging.is_empty());

        // The marker on `applies` answers for exactly this call, so it is
        // needed, not redundant.
        let verdicts = program_verified_function_termination_rules(
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
            TerminationRefusal::DivergingContract {
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
        let bare = |name: &str| VerifiedFunctionRule {
            pointer_result: None,
            loop_semantics: LoopSemantics::ApplyVerifiedRules,
            checked_callees: None,
            applied_tactics: Default::default(),
            function: ProgramFunction::new(
                ProgramType::Void,
                name,
                Vec::new(),
                crate::kernel::program_while(
                    crate::kernel::program_expression::int32_literal(0),
                    Vec::new(),
                    ProgramStatement::Skip,
                ),
            ),
        };
        let rules = [bare("counts"), rule("summarized", &[], 1)];
        let plan = program_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert_eq!(terminating(&verdicts), BTreeSet::from(["counts"]));
        assert_eq!(
            verdicts.refusals["summarized"],
            TerminationRefusal::UnrankedLoop { index: 0 }
        );

        // The same bare loop in a body with no rule of its own: a helper the
        // verified caller reaches.
        let helper = bare("helper").function.with_inline_body();
        let caller = [rule("caller", &["helper"], 0)];
        let bodies = [&helper];
        let plan = program_termination_height_plan(&caller, &bodies);
        let verdicts = program_verified_function_termination_rules(
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
            TerminationRefusal::UnrankedLoop { index: 0 }
        );
    }

    /// A loop whose only annotation is the inherited frame check ran
    /// concretely if the rule was certified under `ApplyVerifiedRules` and no
    /// loop rule names it; certified under `Verify` it may have been
    /// summarized, and a loop a rule names was.
    #[test]
    fn a_frame_checked_loop_is_granted_only_from_a_concrete_certification() {
        let framed = crate::kernel::program_while_with_invariant_and_effect_checks(
            crate::kernel::program_expression::int32_literal(0),
            Vec::new(),
            Vec::new(),
            vec![crate::kernel::LoopEffectCheck::new_with_origin(
                crate::kernel::LoopEffect::Mutable(Vec::new()),
                crate::kernel::LoopEffectSpan::Whole,
                LoopEffectOrigin::InheritedResourceDerived,
                None,
            )],
            ProgramStatement::Skip,
        );
        let function = ProgramFunction::new(ProgramType::Void, "f", Vec::new(), framed);
        let none = BTreeSet::new();
        assert_eq!(
            loops_executed_to_exit(&function, LoopSemantics::ApplyVerifiedRules, &none),
            BTreeSet::from([0])
        );
        assert!(loops_executed_to_exit(&function, LoopSemantics::Verify, &none).is_empty());
        assert!(
            loops_executed_to_exit(
                &function,
                LoopSemantics::ApplyVerifiedRules,
                &BTreeSet::from([0])
            )
            .is_empty()
        );
        let explicit = crate::kernel::program_while_with_invariant_and_effect_checks(
            crate::kernel::program_expression::int32_literal(0),
            Vec::new(),
            Vec::new(),
            vec![crate::kernel::LoopEffectCheck::new_with_origin(
                crate::kernel::LoopEffect::Mutable(Vec::new()),
                crate::kernel::LoopEffectSpan::Whole,
                LoopEffectOrigin::Explicit,
                None,
            )],
            ProgramStatement::Skip,
        );
        let function = ProgramFunction::new(ProgramType::Void, "f", Vec::new(), explicit);
        assert!(
            loops_executed_to_exit(&function, LoopSemantics::ApplyVerifiedRules, &none).is_empty()
        );
    }

    /// The indices name source loops, so nothing is granted when the
    /// certified body's loops are not the source body's loops.
    #[test]
    fn executed_loops_are_granted_only_when_the_bodies_agree() {
        let spin = |condition: u32| {
            crate::kernel::program_while(
                crate::kernel::program_expression::int32_literal(condition),
                Vec::new(),
                ProgramStatement::Skip,
            )
        };
        let agrees = ProgramFunction::new(ProgramType::Void, "f", Vec::new(), spin(0));
        assert_eq!(
            loops_executed_to_exit(&agrees, LoopSemantics::Verify, &BTreeSet::new()),
            BTreeSet::from([0])
        );
        let differs = ProgramFunction::new(ProgramType::Void, "f", Vec::new(), spin(0))
            .with_source_body(spin(1));
        assert!(
            loops_executed_to_exit(&differs, LoopSemantics::Verify, &BTreeSet::new()).is_empty()
        );
        let summarized =
            ProgramFunction::new(ProgramType::Void, "f", Vec::new(), summarized_loop(0))
                .with_source_body(spin(0));
        assert!(
            loops_executed_to_exit(&summarized, LoopSemantics::Verify, &BTreeSet::new()).is_empty()
        );
    }

    /// An empty loop clause still summarizes the loop. Its indexed rule is
    /// not evidence that concrete execution ran every path to an exit.
    #[test]
    fn an_empty_checked_loop_rule_is_not_concrete_termination_evidence() {
        let body = crate::kernel::program_while(
            crate::kernel::program_expression::int32_literal(1),
            Vec::new(),
            ProgramStatement::Skip,
        );
        let function = ProgramFunction::new(ProgramType::Void, "spin", Vec::new(), body);
        for semantics in [LoopSemantics::Verify, LoopSemantics::ApplyVerifiedRules] {
            assert!(loops_executed_to_exit(&function, semantics, &BTreeSet::from([0])).is_empty());
        }
    }

    /// `realloc` is modeled by execution itself, so it is no node of the call
    /// graph and needs no assumption to return.
    #[test]
    fn the_modeled_realloc_returns_without_being_assumed() {
        let rules = [rule("grows", &["realloc"], 0)];
        let plan = program_termination_height_plan(&rules, &[]);
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
        let plan = program_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert_eq!(
            verdicts.refusals["two_loops"],
            TerminationRefusal::UnrankedLoop { index: 0 }
        );

        let mut ranks_second = FunctionTerminationPlan {
            function_name: "two_loops".to_string(),
            recursive_measure: None,
            loop_measures: BTreeMap::new(),
        };
        ranks_second.extend_loop_measures([(
            1,
            LoopTerminationMeasure::Ranking(vec![RankingMeasureKey::ProgramExpression(
                ProgramExpression::Variable("n".to_string()),
            )]),
        )]);
        let error = check(&rules, &[ranks_second], &plan, &[])
            .expect_err("loop 1 is planned but was never certified");
        assert!(
            error.message.contains("no verified loop rule"),
            "loop 1 exists and must be reported as uncertified, got {error}"
        );
    }

    /// The planner keeps its own stack, and the check visits each function
    /// once, so a call chain as long as the project is neither a machine
    /// stack overflow nor a quadratic walk.
    #[test]
    #[ignore = "nightly: 1.0s in the parallel gate"]
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
        let plan = program_termination_height_plan(&rules, &[]);
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
    ) -> VerifiedFunctionRule {
        let mut body = ProgramStatement::Skip;
        for callee in std::iter::once(&name).chain(callees) {
            let call = crate::kernel::program_call(*callee, Vec::new());
            let call = if in_loop {
                crate::kernel::program_while(
                    crate::kernel::program_expression::int32_literal(1),
                    Vec::new(),
                    call,
                )
            } else {
                call
            };
            body = ProgramStatement::seq(Arc::new(body), Arc::new(call));
        }
        let mut function = ProgramFunction::new(ProgramType::Void, name, Vec::new(), body);
        if measure {
            function = function.with_recursion_measure(vec![RankingComponent::Pure {
                source: "level(n)".to_string(),
                expression: SpecExpression::ProgramExpression(ProgramExpression::Variable(
                    "n".to_string(),
                )),
            }]);
        }
        if inline {
            function = function.with_inline_body();
        }
        VerifiedFunctionRule {
            pointer_result: None,
            function,
            loop_semantics: LoopSemantics::ApplyVerifiedRules,
            checked_callees: None,
            applied_tactics: Default::default(),
        }
    }

    fn expression_plan(name: &str) -> FunctionTerminationPlan {
        FunctionTerminationPlan {
            function_name: name.to_string(),
            recursive_measure: Some(FunctionTerminationMeasure::Expression(
                "level(n)".to_string(),
            )),
            loop_measures: BTreeMap::new(),
        }
    }

    /// A tactic rule: a procedure whose body runs no code, recursing only
    /// through the applications its certified proof recorded.
    fn tactic_rule(name: &str, measure: bool) -> VerifiedFunctionRule {
        let mut function = ProgramFunction::new(
            ProgramType::Void,
            name,
            Vec::new(),
            ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)),
        );
        if measure {
            function = function.with_recursion_measure(vec![RankingComponent::Pure {
                source: "level(n)".to_string(),
                expression: SpecExpression::ProgramExpression(ProgramExpression::Variable(
                    "n".to_string(),
                )),
            }]);
        }
        VerifiedFunctionRule {
            pointer_result: None,
            function,
            loop_semantics: LoopSemantics::ApplyVerifiedRules,
            checked_callees: None,
            applied_tactics: BTreeSet::from([name.to_string()]),
        }
    }

    /// A tactic's recursion is in its proof, not its body, so the recorded
    /// application is its only recursive edge. With no measure it is refused
    /// as unranked recursion, never accepted as a call-free function.
    #[test]
    fn a_tactic_recursing_through_its_applications_needs_a_measure() {
        let rules = [tactic_rule("convert", false)];
        let plan = program_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[], &plan, &[]).expect("the plan checks");
        assert!(terminating(&verdicts).is_empty());
        assert!(matches!(
            verdicts.refusals.get("convert"),
            Some(TerminationRefusal::UnmeasuredRecursion { .. })
        ));
    }

    /// A parameter measure reads recursive calls in a body, and a tactic's
    /// body has none; ranking its recursion that way would rank nothing.
    #[test]
    fn a_tactic_recursing_through_its_applications_refuses_a_parameter_measure() {
        let rules = [tactic_rule("convert", false)];
        let plan = program_termination_height_plan(&rules, &[]);
        let error = check(
            &rules,
            &[FunctionTerminationPlan {
                function_name: "convert".to_string(),
                recursive_measure: Some(FunctionTerminationMeasure::NumericParameter(0)),
                loop_measures: BTreeMap::new(),
            }],
            &plan,
            &[],
        )
        .expect_err("a tactic's recursion has no body call for a parameter measure to read");
        assert!(
            error
                .message
                .contains("recurses through a tactic application"),
            "{error}"
        );
    }

    /// An expression measure's descent was owed at the recorded application
    /// itself, so it ranks a tactic's recursion.
    #[test]
    fn a_tactic_recursing_through_its_applications_is_ranked_by_an_expression() {
        let rules = [tactic_rule("convert", true)];
        let plan = program_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[expression_plan("convert")], &plan, &[])
            .expect("the expression measure ranks the recorded recursion");
        assert_eq!(terminating(&verdicts), BTreeSet::from(["convert"]));
    }

    /// The expression measure certifies direct self-recursion. Nothing about
    /// the body is analysed: the descent rides on obligations the call steps
    /// raised while this rule was being certified.
    #[test]
    fn an_expression_measure_ranks_direct_self_recursion() {
        let rules = [recursive_rule("drain", &[], true, false, false)];
        let plan = program_termination_height_plan(&rules, &[]);
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
        let plan = program_termination_height_plan(&rules, &[]);
        let error = check(&rules, &[expression_plan("drain")], &plan, &[])
            .expect_err("an undeclared measure must not check");
        assert!(
            error.message.contains("carries no declared measure"),
            "{error}"
        );
    }

    /// The anchor names one function, so a second member of the cycle owes
    /// nothing. Slice 1 refuses such a component rather than certifying a
    /// recursion with an unranked edge.
    #[test]
    fn an_expression_measure_refuses_a_component_whose_peers_are_undeclared() {
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
            "{error}"
        );
    }

    /// Members whose certified interfaces name each other as recursion
    /// peers had every cross-member call ranked under their anchors, so the
    /// component checks; one side naming the other is not enough.
    #[test]
    fn an_expression_measure_ranks_a_component_whose_members_name_each_other() {
        let with_peers = |name: &str, peer: &str, named: bool| {
            let mut rule = recursive_rule(name, &[peer], true, false, false);
            if named {
                rule.function = rule.function.with_recursion_peers(vec![peer.to_string()]);
            }
            rule
        };
        let heights = heights(&[("even", 0), ("odd", 0)]);
        let plans = [expression_plan("even"), expression_plan("odd")];
        let rules = [
            with_peers("even", "odd", true),
            with_peers("odd", "even", true),
        ];
        let verdicts = check(&rules, &plans, &heights, &[])
            .expect("a component whose members name each other checks");
        assert_eq!(terminating(&verdicts), BTreeSet::from(["even", "odd"]));
        let rules = [
            with_peers("even", "odd", true),
            with_peers("odd", "even", false),
        ];
        let error = check(&rules, &plans, &heights, &[])
            .expect_err("a member that does not name its peer leaves an edge unranked");
        assert!(error.message.contains("recursion peer"), "{error}");
    }

    /// A helper with an inline body and a verified rule is called through
    /// that rule, its own self-call included, so the self-call read the
    /// anchor exactly as an ordinary function's does.
    #[test]
    fn an_expression_measure_ranks_an_inline_bodied_helper_with_a_rule() {
        let rules = [recursive_rule("drain", &[], true, true, false)];
        let plan = program_termination_height_plan(&rules, &[]);
        let verdicts = check(&rules, &[expression_plan("drain")], &plan, &[])
            .expect("a ruled inline helper is ranked like any function");
        assert_eq!(terminating(&verdicts), BTreeSet::from(["drain"]));
    }

    /// The `decreases` component `recursive_rule` declares, which is also the
    /// one its ranked loop is ranked by.
    fn declared_component() -> RankingComponent {
        RankingComponent::Pure {
            source: "level(n)".to_string(),
            expression: SpecExpression::ProgramExpression(ProgramExpression::Variable(
                "n".to_string(),
            )),
        }
    }

    /// A rule for `drain`, whose self-call sits inside one summarized loop
    /// ranked by the same component. `loop_measures` is the plan side of that
    /// ranking, so the two agree and the loop is not refused as unranked.
    fn self_call_in_loop_rule(name: &str) -> VerifiedFunctionRule {
        let body = ProgramStatement::seq(
            Arc::new(ProgramStatement::Skip),
            Arc::new(ProgramStatement::While {
                condition: crate::kernel::program_expression::int32_literal(1),
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
                backedge_target: None,
                natural_exit_target: None,
                body: Box::new(crate::kernel::program_call(name, Vec::new())),
            }),
        );
        VerifiedFunctionRule {
            pointer_result: None,
            function: ProgramFunction::new(ProgramType::Void, name, Vec::new(), body)
                .with_recursion_measure(vec![declared_component()]),
            loop_semantics: LoopSemantics::ApplyVerifiedRules,
            checked_callees: None,
            applied_tactics: Default::default(),
        }
    }

    /// The plan for [`self_call_in_loop_rule`]: the expression measure for the
    /// recursion, and the same component as loop 0's own ranking.
    fn self_call_in_loop_plan(name: &str) -> FunctionTerminationPlan {
        FunctionTerminationPlan {
            loop_measures: BTreeMap::from([(
                0,
                LoopTerminationMeasure::Ranking(vec![declared_component().key()]),
            )]),
            ..expression_plan(name)
        }
    }

    /// The certified rule for that loop, carrying `anchor`.
    ///
    /// Only the kernel writes `recursion_anchor`, from the environment the
    /// paths were produced in; the struct is assembled directly here because
    /// this test is inside the kernel.
    fn loop_rule_for(
        function: &ProgramFunction,
        anchor: Option<RecursionAnchor>,
    ) -> VerifiedLoopRule {
        let ProgramStatement::Seq(statements) = &function.source_body else {
            unreachable!("`self_call_in_loop_rule` builds a sequence");
        };
        VerifiedLoopRule {
            symbolic_entry_state: ExecutionState::default(),
            loop_statement: statements.rest().as_ref().clone(),
            loop_index: Some(0),
            required_assumptions: PureFactContext::new(),
            paths: Vec::new(),
            composite_resource_definitions: Vec::new(),
            recursion_anchor: anchor.map(Arc::new),
            variable_index: Default::default(),
        }
    }

    #[test]
    fn loop_strategies_own_independent_measures_and_need_every_path_ranked() {
        let function = self_call_in_loop_rule("drain").function;
        let first = loop_rule_for(&function, None);
        let mut second = first.clone();
        let ProgramStatement::While {
            ranking_measures, ..
        } = &mut second.loop_statement
        else {
            unreachable!();
        };
        *ranking_measures = vec![RankingComponent::Pure {
            source: "other_level(n)".into(),
            expression: SpecExpression::ProgramExpression(ProgramExpression::Variable("n".into())),
        }];
        let (ranked, unranked) = verified_loop_ranking_measures(
            "drain",
            &function.source_body,
            &[first.clone(), second.clone()],
        )
        .expect("independent strategies need not name the same measure");
        assert_eq!(ranked[&0].len(), 2);
        assert!(unranked.is_empty());
        check_loops(
            &function.source_body,
            &BTreeMap::new(),
            &ranked,
            "drain",
            &mut 0,
            &mut Vec::new(),
        )
        .unwrap();
        // A separately supplied declaration can name either owned measure.
        for measure in &ranked[&0] {
            check_loops(
                &function.source_body,
                &BTreeMap::from([(0, measure.clone())]),
                &ranked,
                "drain",
                &mut 0,
                &mut Vec::new(),
            )
            .unwrap();
        }
        let ProgramStatement::While {
            ranking_measures, ..
        } = &mut second.loop_statement
        else {
            unreachable!();
        };
        ranking_measures.clear();
        for rules in [[first.clone(), second.clone()], [second, first]] {
            let (ranked, unranked) =
                verified_loop_ranking_measures("drain", &function.source_body, &rules).unwrap();
            assert!(ranked.is_empty(), "a ranked sibling cannot cover this path");
            assert_eq!(unranked, BTreeSet::from([0]));
        }
    }

    #[test]
    fn generation_opens_recursion_and_loop_requirements_without_proving_them() {
        let rules = [self_call_in_loop_rule("drain")];
        let plans = [self_call_in_loop_plan("drain")];
        let goals = obligations::TerminationObligations::generate(
            &rules,
            &plans,
            &BTreeMap::new(),
            &[],
            &program_termination_height_plan(&rules, &[]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
            false,
        )
        .expect("generation does not attempt the missing loop-anchor proof");
        let function = &goals.function_goals["drain"];
        assert_eq!(function.loop_indices, [0]);
        assert_eq!(
            function.recursive_callees,
            BTreeSet::from(["drain".to_string()])
        );
        assert!(
            matches!(&function.calls[0], obligations::TerminationCallObligation::Callee { callee, recursive: true } if callee == "drain")
        );
        let error = goals
            .prove_implicitly()
            .expect_err("execution must prove the already opened loop-anchor requirement");
        assert!(
            error
                .message
                .contains("certified without `drain`'s recursion anchor"),
            "{error}"
        );
        assert_eq!(error.function(), Some("drain"));
    }

    fn anchor_for(name: &str) -> RecursionAnchor {
        RecursionAnchor {
            function: name.to_string(),
            components: vec![declared_component()],
            peers: Vec::new(),
            structural_entry: None,
            measure: vec![RankingMeasureValue::Machine(MachineTerm::constant(7))],
            entry_obligations: Vec::new(),
        }
    }

    fn check_with_loop_rules(
        rules: &[VerifiedFunctionRule],
        plans: &[FunctionTerminationPlan],
        loop_rules: &BTreeMap<String, Vec<VerifiedLoopRule>>,
    ) -> Result<TerminationVerdicts, TerminationError> {
        program_verified_function_termination_rules(
            rules,
            plans,
            loop_rules,
            &[],
            &program_termination_height_plan(rules, &[]),
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
            "{error}"
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
            "{error}"
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
            "{error}"
        );
    }

    /// `decreases <parameter>` is untouched: it still resolves the index
    /// against the verified function and analyses the recursion paths.
    #[test]
    fn a_parameter_measure_is_unaffected_by_a_declared_expression_measure() {
        let rules = [recursive_rule("drain", &[], false, false, false)];
        let plan = program_termination_height_plan(&rules, &[]);
        let numeric = FunctionTerminationPlan {
            function_name: "drain".to_string(),
            recursive_measure: Some(FunctionTerminationMeasure::NumericParameter(0)),
            loop_measures: BTreeMap::new(),
        };
        let error = check(&rules, &[numeric], &plan, &[])
            .expect_err("`drain` has no parameter to rank, as before");
        assert!(
            error
                .message
                .contains("termination parameter index is invalid"),
            "{error}"
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/termination/local_descent_tests.rs");
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
    fn calls_body(callees: &[String]) -> ProgramStatement {
        match callees {
            [] => ProgramStatement::Skip,
            [only] => crate::kernel::program_call(only.clone(), Vec::new()),
            _ => {
                let (left, right) = callees.split_at(callees.len() / 2);
                ProgramStatement::seq(Arc::new(calls_body(left)), Arc::new(calls_body(right)))
            }
        }
    }

    /// A verified rule whose body calls `callees` and nothing else, which is
    /// all the termination check reads of a function carrying no loops and no
    /// measures.
    fn rule(name: &str, callees: &[String]) -> VerifiedFunctionRule {
        VerifiedFunctionRule {
            pointer_result: None,
            function: ProgramFunction::new(
                ProgramType::Void,
                name,
                Vec::new(),
                calls_body(callees),
            ),
            loop_semantics: LoopSemantics::ApplyVerifiedRules,
            checked_callees: None,
            applied_tactics: Default::default(),
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
        rules: &[VerifiedFunctionRule],
        inspect: impl FnOnce(&BTreeMap<String, usize>, &TerminationVerdicts),
    ) -> Sample {
        let (heights, plan_work) = crate::instrumentation::measure_deterministic_work(|| {
            program_termination_height_plan(rules, &[])
        });
        let (verdicts, check_work) = crate::instrumentation::measure_deterministic_work(|| {
            program_verified_function_termination_rules(
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

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/termination/termination_scaling_tests.rs");
    }
}

#[cfg(test)]
mod checked_callee_certification_tests {
    use super::*;

    #[test]
    fn checked_callee_graph_distinguishes_missing_and_empty_evidence() {
        let rule = |checked_callees| VerifiedFunctionRule {
            pointer_result: None,
            function: ProgramFunction::new(
                ProgramType::Void,
                "caller",
                vec![],
                crate::kernel::program_call("callee", vec![]),
            ),
            loop_semantics: LoopSemantics::ApplyVerifiedRules,
            applied_tactics: Default::default(),
            checked_callees,
        };
        let empty = rule(Some(Arc::new(BTreeSet::new())));
        let missing = rule(None);
        assert!(termination_call_graph(std::slice::from_ref(&empty), &[]).1["caller"].is_empty());
        let expected = BTreeSet::from(["callee".to_string()]);
        assert_eq!(
            termination_call_graph(std::slice::from_ref(&missing), &[]).1["caller"],
            expected
        );
        // Name-keyed function selection and metadata selection must agree,
        // including when the selected rule lacks dependency evidence.
        assert_eq!(
            termination_call_graph(&[empty, missing], &[]).1["caller"],
            expected
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/termination/checked_callee_certification_tests.rs");
    }
}

#[cfg(test)]
mod spec_walk_oracle_tests;
