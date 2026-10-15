//! Exhaustive structural child walks for C source analyses and linked metadata.
//! Immutable and mutable walks share the same matches, so new syntax cannot
//! silently disappear from either kind of pass.
use super::{C0Expression, C0Statement};

macro_rules! child_walkers {
    ($expressions_fn:ident, $statements_fn:ident, $iter:ident, $as_ref:ident, $($mutable:tt)*) => {
        /// The immediate subexpressions and substatements of one expression.
        pub(crate) fn $expressions_fn<'a>(
            expression: &'a $($mutable)* C0Expression,
            expressions: &mut Vec<&'a $($mutable)* C0Expression>,
            statements: &mut Vec<&'a $($mutable)* C0Statement>,
        ) {
            match expression {
                C0Expression::ScalarUpdate { .. } => {}
                C0Expression::Void
                | C0Expression::Variable(_)
                | C0Expression::FunctionAddress(_)
                | C0Expression::Int32Literal(_)
                | C0Expression::UInt8Literal(_)
                | C0Expression::UInt32Literal(_)
                | C0Expression::Int64Literal(_)
                | C0Expression::UInt64Literal(_)
                | C0Expression::Float32Literal(_)
                | C0Expression::Float64Literal(_)
                | C0Expression::SizeOfStruct { .. }
                | C0Expression::SizeOfUnion { .. }
                | C0Expression::SizeOfType { .. } => {}
                C0Expression::Call { arguments, .. } => expressions.extend(arguments.$iter()),
                C0Expression::IndirectCall {
                    function,
                    arguments,
                    ..
                } => {
                    expressions.push(function);
                    expressions.extend(arguments.$iter());
                }
                C0Expression::Assignment { value, .. } => expressions.push(value),
                C0Expression::StatementExpression { body, value, .. } => {
                    statements.push(body);
                    expressions.push(value);
                }
                C0Expression::Cast { expression, .. }
                | C0Expression::FloatNegate(expression)
                | C0Expression::FloatClassification { expression, .. }
                | C0Expression::AddressOf(expression)
                | C0Expression::PointerOffsetBytes {
                    pointer: expression,
                    ..
                }
                | C0Expression::MemberAddress {
                    pointer: expression,
                    ..
                }
                | C0Expression::Not(expression)
                | C0Expression::BitwiseNot(expression)
                | C0Expression::Load(expression)
                | C0Expression::SequentialRead {
                    target: expression, ..
                }
                | C0Expression::AggregateAddress {
                    pointer: expression,
                    ..
                }
                | C0Expression::Field {
                    pointer: expression,
                    ..
                }
                | C0Expression::UnionField {
                    pointer: expression,
                    ..
                }
                | C0Expression::UnionAddress {
                    pointer: expression,
                    ..
                }
                | C0Expression::CheckedArrayIndex {
                    index: expression, ..
                } => expressions.push(expression),
                C0Expression::Conditional {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    expressions.push(condition);
                    expressions.push(then_branch);
                    expressions.push(else_branch);
                }
                C0Expression::SequentialWrite { target, value, .. } => {
                    expressions.push(target);
                    expressions.push(value);
                }
                crate::languages::c::syntax::binary_c0_expression!(left, right) => {
                    expressions.push(left);
                    expressions.push(right);
                }
            }
        }

        /// The immediate subexpressions and substatements of one statement.
        pub(crate) fn $statements_fn<'a>(
            statement: &'a $($mutable)* C0Statement,
            expressions: &mut Vec<&'a $($mutable)* C0Expression>,
            statements: &mut Vec<&'a $($mutable)* C0Statement>,
        ) {
            match statement {
                C0Statement::Skip
                | C0Statement::Break
                | C0Statement::Continue
                | C0Statement::Goto { .. }
                | C0Statement::Declare {
                    initializer: None, ..
                }
                | C0Statement::DeclareStructValue { .. } => {}
                C0Statement::Label { statement, .. } => statements.push(statement),
                C0Statement::Scope { body } => statements.push(body),
                C0Statement::Declare {
                    initializer: Some(expression),
                    ..
                }
                | C0Statement::Assign { expression, .. } => expressions.push(expression),
                C0Statement::CallAssign { arguments, .. } | C0Statement::Call { arguments, .. } => {
                    expressions.extend(arguments.$iter());
                }
                C0Statement::IndirectCall {
                    function,
                    arguments,
                    ..
                } => {
                    expressions.push(function);
                    expressions.extend(arguments.$iter());
                }
                C0Statement::HeapAllocate { bytes, .. } => expressions.push(bytes),
                C0Statement::HeapFree { pointer, .. } => expressions.push(pointer),
                C0Statement::Assert { condition, .. } => expressions.push(condition),
                C0Statement::Seq(first, second) => {
                    statements.push(first);
                    statements.push(second);
                }
                C0Statement::Return(value, _) => expressions.push(value),
                C0Statement::Store { pointer, value, .. } => {
                    expressions.push(pointer);
                    expressions.push(value);
                }
                C0Statement::SequentialStore { target, value, .. }
                | C0Statement::AggregateCopy {
                    target,
                    source: value,
                    ..
                } => {
                    expressions.push(target);
                    expressions.push(value);
                }
                C0Statement::Update {
                    target, operand, ..
                } => {
                    expressions.push(target);
                    expressions.push(operand);
                }
                C0Statement::If {
                    condition,
                    then_branch,
                    else_branch,
                    ..
                } => {
                    expressions.push(condition);
                    statements.push(then_branch);
                    statements.push(else_branch);
                }
                C0Statement::While {
                    condition, body, ..
                }
                | C0Statement::DoWhile {
                    condition, body, ..
                } => {
                    expressions.push(condition);
                    statements.push(body);
                }
                C0Statement::For {
                    initializer,
                    condition,
                    step,
                    body,
                    ..
                } => {
                    statements.push(initializer);
                    expressions.push(condition);
                    statements.push(step);
                    statements.push(body);
                }
                C0Statement::Switch {
                    expression, cases, ..
                } => {
                    expressions.push(expression);
                    statements.extend(cases.$iter().map(|case| case.body.$as_ref()));
                }
            }
        }


    };
}
child_walkers!(child_expressions, child_statements, iter, as_ref,);
child_walkers!(
    child_expressions_mut,
    child_statements_mut,
    iter_mut,
    as_mut,
    mut
);
