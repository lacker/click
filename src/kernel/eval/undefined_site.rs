//! Where in a refused statement its undefined behavior arises.
//!
//! A statement transition reports undefined behavior by kind only. When a
//! step is refused for it, the diagnostic names the operation as well: the
//! statement's expressions are evaluated again at its entry state, innermost
//! first, and the first one whose own evaluation has a path with the same
//! kind is the site. This runs only to word a refusal, never while checking.

use super::*;

/// The part of a statement whose evaluation has the reported undefined
/// behavior.
#[derive(Clone, Debug)]
pub(crate) enum CUndefinedBehaviorSite {
    /// An expression the statement evaluates.
    Expression(CExpression),
    /// The store through this pointer expression, when no operand of the
    /// store has the behavior itself.
    Store(CExpression),
}

/// The innermost operation of `statement` that has `kind` at `state`, or
/// `None` when no single operation can be named.
///
/// The search never descends into an operand that a guard decides whether
/// to evaluate (the right side of `&&` and `||`, the arms of `?:`), nor
/// into the place an `&` names, so it never blames an operation the
/// statement does not run. Such an operand is reported through the
/// expression that contains it.
pub(crate) fn locate_undefined_behavior(
    state: &CState,
    statement: &CStatement,
    assumptions: &PureFactContext,
    kind: &CUndefinedBehavior,
) -> Option<CUndefinedBehaviorSite> {
    let mut expressions = Vec::new();
    statement_expressions(statement, &mut expressions);
    for (expression, condition) in expressions {
        if let Some(site) = innermost_site(state, expression, condition, assumptions, kind) {
            return Some(CUndefinedBehaviorSite::Expression(site.clone()));
        }
    }
    match statement {
        CStatement::Store { pointer, .. } | CStatement::TypedStore { pointer, .. } => {
            Some(CUndefinedBehaviorSite::Store(pointer.clone()))
        }
        _ => None,
    }
}

/// [`locate_undefined_behavior`] for a controlling expression evaluated on
/// its own, as a branch or loop condition is.
pub(crate) fn locate_undefined_behavior_in_condition(
    state: &CState,
    condition: &CExpression,
    assumptions: &PureFactContext,
    kind: &CUndefinedBehavior,
) -> Option<CUndefinedBehaviorSite> {
    innermost_site(state, condition, true, assumptions, kind)
        .map(|site| CUndefinedBehaviorSite::Expression(site.clone()))
}

/// The expressions `statement` evaluates itself, each with whether its value
/// is tested for truth. Nested statement bodies are not stepped with it.
fn statement_expressions<'a>(
    statement: &'a CStatement,
    expressions: &mut Vec<(&'a CExpression, bool)>,
) {
    match statement {
        CStatement::Declare {
            initializer: Some(expression),
            ..
        }
        | CStatement::Assign { expression, .. }
        | CStatement::HeapAllocate {
            bytes: expression, ..
        }
        | CStatement::HeapFree {
            pointer: expression,
        }
        | CStatement::Return(expression)
        | CStatement::Throw(expression)
        | CStatement::Switch { expression, .. } => expressions.push((expression, false)),
        CStatement::Assert { condition, .. }
        | CStatement::If { condition, .. }
        | CStatement::While { condition, .. } => expressions.push((condition, true)),
        CStatement::CallAssign { arguments, .. } | CStatement::Call { arguments, .. } => {
            expressions.extend(arguments.iter().map(|argument| (argument, false)));
        }
        CStatement::Store { pointer, value } | CStatement::TypedStore { pointer, value, .. } => {
            expressions.push((pointer, false));
            expressions.push((value, false));
        }
        CStatement::CopyAggregate { target, source, .. }
        | CStatement::InitializeScalarArray { target, source, .. } => {
            expressions.push((target, false));
            expressions.push((source, false));
        }
        CStatement::Update { operand, .. } => expressions.push((operand, false)),
        CStatement::ForStep { step, .. } => statement_expressions(step, expressions),
        CStatement::Seq(first, _) => statement_expressions(first, expressions),
        CStatement::Scope { body } => statement_expressions(body, expressions),
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare {
            initializer: None, ..
        }
        | CStatement::DeclareAggregate { .. }
        | CStatement::TryCatchInt32 { .. }
        | CStatement::EndAutomaticLifetimes { .. } => {}
    }
}

fn innermost_site<'a>(
    state: &CState,
    expression: &'a CExpression,
    condition: bool,
    assumptions: &PureFactContext,
    kind: &CUndefinedBehavior,
) -> Option<&'a CExpression> {
    let mut children = Vec::new();
    unconditional_operands(expression, &mut children);
    for child in children {
        if let Some(site) = innermost_site(state, child, false, assumptions, kind) {
            return Some(site);
        }
    }
    has_undefined_behavior(state, expression, condition, assumptions, kind).then_some(expression)
}

fn has_undefined_behavior(
    state: &CState,
    expression: &CExpression,
    condition: bool,
    assumptions: &PureFactContext,
    kind: &CUndefinedBehavior,
) -> bool {
    let mut budget = ExecutionBudget::beside_live_state();
    let paths = if condition {
        evaluate_c_condition_paths(state, expression, assumptions, &mut budget)
    } else {
        evaluate_c_expression_paths(state, expression, assumptions, &mut budget)
    };
    paths.is_ok_and(|paths| {
        paths.iter().any(|path| {
            matches!(&path.outcome, CExpressionOutcome::UndefinedBehavior(found)
                if std::mem::discriminant(found) == std::mem::discriminant(kind))
        })
    })
}

/// The operands of `expression` that are evaluated whenever it is.
fn unconditional_operands<'a>(expression: &'a CExpression, operands: &mut Vec<&'a CExpression>) {
    match expression {
        CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_) => {}
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
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
        } => operands.push(expression),
        CExpression::PointerAligned { pointer, .. } => operands.push(pointer),
        CExpression::MemberAddress { object, .. } => operands.push(object),
        CExpression::ArrayRowAddress { array, index, .. } => {
            operands.push(array);
            operands.push(index);
        }
        CExpression::RecordPointerOffset { pointer, index, .. } => {
            operands.push(pointer);
            operands.push(index);
        }
        CExpression::Conditional { condition, .. } => operands.push(condition),
        CExpression::And(left, _) | CExpression::Or(left, _) => operands.push(left),
        CExpression::AddressOf(place) | CExpression::CheckedObjectAddress(place) => {
            place_address_operands(place, operands);
        }
        CExpression::LessThan(left, right)
        | CExpression::LessEqual(left, right)
        | CExpression::GreaterThan(left, right)
        | CExpression::GreaterEqual(left, right)
        | CExpression::Equal(left, right)
        | CExpression::NotEqual(left, right)
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
            operands.push(left);
            operands.push(right);
        }
    }
}

/// The operands evaluated to form the address of `place` without reading
/// it: the pointer of `*p`, and the base and index of `a[i]`.
fn place_address_operands<'a>(place: &'a CExpression, operands: &mut Vec<&'a CExpression>) {
    match place {
        CExpression::Load(pointer) | CExpression::TypedLoad { pointer, .. } => {
            operands.push(pointer);
        }
        CExpression::Index(base, index) => {
            operands.push(base);
            operands.push(index);
        }
        _ => {}
    }
}
