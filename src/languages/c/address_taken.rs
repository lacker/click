//! Which automatic objects a program can form the address of.
//!
//! One conservative syntactic pass over every parsed function body, run before
//! any verification query, so that the kernel can decide that a pointer value
//! it cannot resolve does not designate a local the program never addresses.
//! The answer is a set of *names* and is deliberately program-wide;
//! [`crate::kernel::primitives::block_is_never_address_taken_local`] says why,
//! and carries the soundness argument for spending it.
//!
//! The pass is default-deny in both directions. A name is reported only if
//! every declaration of it, in every function, is scalar or pointer typed, and
//! it never occurs anywhere under an address-forming node. Anything the walk
//! cannot account for — a function whose body it did not see, a name it never
//! saw declared, a synthetic name the verifier mints — is simply absent from
//! the result, which is the same as being addressable.
//!
//! The two structural walks below (`child_expressions`, `child_statements`)
//! are the only exhaustive matches: a syntax form added later must be added to
//! them, and until it is, the compiler refuses to build rather than letting
//! the pass walk past it.

use std::collections::BTreeSet;

use super::syntax::{C0Expression, C0Function, C0Statement, C0SwitchCase, C0Type};

/// What one pass learned about one bundle of parsed function bodies.
pub struct AddressTakenSummary {
    /// Every name declared as an automatic object with a scalar or pointer
    /// type, anywhere in the bundle.
    scalar_declarations: BTreeSet<String>,
    /// Every name the bundle can form an address of: declared with an
    /// aggregate type somewhere, so that its name converts to a pointer on
    /// use, or occurring anywhere under an address-forming node.
    taken: BTreeSet<String>,
}

impl AddressTakenSummary {
    /// The names no function in this bundle can form the address of.
    pub fn never_taken(&self) -> BTreeSet<String> {
        self.scalar_declarations
            .difference(&self.taken)
            .cloned()
            .collect()
    }

    /// The names this bundle shows to be addressable. A name absent from both
    /// sets was never declared here and is addressable by default.
    pub fn taken(&self) -> &BTreeSet<String> {
        &self.taken
    }
}

/// Runs the pass over every function in a parsed source bundle.
///
/// A function whose body the C frontend did not produce contributes no
/// declarations, which is the safe direction for an external declaration: it
/// has no automatic objects of this program at all. A function carrying a
/// pre-lowered kernel body from another frontend is different — it has
/// executable semantics this walk cannot read, and those semantics may address
/// a name any other function declares — so one of those empties the result
/// instead.
pub fn summarize_address_taken<'a>(
    functions: impl IntoIterator<Item = &'a C0Function>,
) -> AddressTakenSummary {
    let mut summary = AddressTakenSummary {
        scalar_declarations: BTreeSet::new(),
        taken: BTreeSet::new(),
    };
    let mut unreadable_body = false;
    for function in functions {
        if function.prelowered_kernel_function().is_some() {
            unreadable_body = true;
            continue;
        }
        for parameter in function.parameters() {
            declare(&mut summary, parameter.name(), parameter.c_type());
        }
        walk_statement(function.body(), &mut summary);
    }
    if unreadable_body {
        summary.scalar_declarations.clear();
    }
    summary
}

/// Records one automatic declaration. An aggregate or array object's name
/// converts to its address wherever it is used, so declaring one is itself a
/// way for the program to hold that address; such a name is refused rather
/// than tracked.
fn declare(summary: &mut AddressTakenSummary, name: &str, c_type: C0Type) {
    if scalar_or_pointer(c_type) {
        summary.scalar_declarations.insert(name.to_string());
    } else {
        summary.taken.insert(name.to_string());
    }
}

/// Whether an object of this type is read and written as a value rather than
/// through its address. Listed exhaustively on purpose: a type added later
/// lands in the `false` arm, which refuses the name.
fn scalar_or_pointer(c_type: C0Type) -> bool {
    match c_type {
        C0Type::Int8 | C0Type::Int8Pointer | C0Type::Int8PointerPointer => true,
        C0Type::Char
        | C0Type::Bool
        | C0Type::Int16
        | C0Type::Int32
        | C0Type::UInt8
        | C0Type::UInt16
        | C0Type::UInt32
        | C0Type::Int64
        | C0Type::UInt64
        | C0Type::Float32
        | C0Type::Float64
        | C0Type::VoidPointer
        | C0Type::VoidPointerPointer
        | C0Type::CharPointer
        | C0Type::CharPointerPointer
        | C0Type::Int16Pointer
        | C0Type::UInt16Pointer
        | C0Type::Int32Pointer
        | C0Type::UInt8Pointer
        | C0Type::UInt32Pointer
        | C0Type::Int64Pointer
        | C0Type::UInt64Pointer
        | C0Type::Float32Pointer
        | C0Type::Float64Pointer
        | C0Type::Int16PointerPointer
        | C0Type::UInt16PointerPointer
        | C0Type::Int32PointerPointer
        | C0Type::UInt8PointerPointer
        | C0Type::UInt32PointerPointer
        | C0Type::Int64PointerPointer
        | C0Type::UInt64PointerPointer
        | C0Type::Float32PointerPointer
        | C0Type::Float64PointerPointer
        | C0Type::FunctionPointer(_) => true,
        C0Type::Int8Array(_) => false,
        C0Type::Void
        | C0Type::CharArray(_)
        | C0Type::Int32Array(_)
        | C0Type::UInt8Array(_)
        | C0Type::Int16Array(_)
        | C0Type::UInt16Array(_)
        | C0Type::UInt32Array(_)
        | C0Type::Int64Array(_)
        | C0Type::UInt64Array(_)
        | C0Type::Float32Array(_)
        | C0Type::Float64Array(_) => false,
    }
}

/// Walks one statement, recording declarations and address-forming nodes.
fn walk_statement(statement: &C0Statement, summary: &mut AddressTakenSummary) {
    if let C0Statement::Declare { name, c_type, .. } = statement {
        declare(summary, name, *c_type);
    }
    // A struct value's name is its address wherever it is used.
    if let C0Statement::DeclareStructValue { name, .. } = statement {
        summary.taken.insert(name.clone());
    }
    let mut expressions = Vec::new();
    let mut statements = Vec::new();
    child_statements(statement, &mut expressions, &mut statements);
    for expression in expressions {
        walk_expression(expression, summary);
    }
    for statement in statements {
        walk_statement(statement, summary);
    }
}

/// Walks one expression, refusing every name under an address-forming node.
///
/// The three address-forming nodes are `&e` and the two aggregate-place nodes
/// the parser uses to carry a struct or union place through member selection.
/// Every name under one of them is refused whatever its shape, so `&x`,
/// `&a[i]`, `&s.f` and `&*p` are all caught, and so is the index in `&a[i]`.
/// The `AddressOf(Variable(_))` test in `src/kernel/termination.rs` catches
/// only the first of those.
fn walk_expression(expression: &C0Expression, summary: &mut AddressTakenSummary) {
    if let C0Expression::AddressOf(inner)
    | C0Expression::AggregateAddress { pointer: inner, .. }
    | C0Expression::UnionAddress { pointer: inner, .. } = expression
    {
        mentioned_names(inner, &mut summary.taken);
        return;
    }
    let mut expressions = Vec::new();
    let mut statements = Vec::new();
    child_expressions(expression, &mut expressions, &mut statements);
    for expression in expressions {
        walk_expression(expression, summary);
    }
    for statement in statements {
        walk_statement(statement, summary);
    }
}

/// Every name an expression mentions, at any depth and through any form,
/// including the names its embedded statements declare and read.
fn mentioned_names(expression: &C0Expression, names: &mut BTreeSet<String>) {
    match expression {
        C0Expression::Variable(name) | C0Expression::Assignment { name, .. } => {
            names.insert(name.clone());
        }
        _ => {}
    }
    let mut expressions = Vec::new();
    let mut statements = Vec::new();
    child_expressions(expression, &mut expressions, &mut statements);
    for expression in expressions {
        mentioned_names(expression, names);
    }
    for statement in statements {
        statement_mentioned_names(statement, names);
    }
}

/// The same for a statement, used for a statement expression under an `&`.
fn statement_mentioned_names(statement: &C0Statement, names: &mut BTreeSet<String>) {
    match statement {
        C0Statement::Declare { name, .. }
        | C0Statement::DeclareStructValue { name, .. }
        | C0Statement::Assign { name, .. }
        | C0Statement::CallAssign { target: name, .. }
        | C0Statement::HeapAllocate { target: name, .. } => {
            names.insert(name.clone());
        }
        _ => {}
    }
    let mut expressions = Vec::new();
    let mut statements = Vec::new();
    child_statements(statement, &mut expressions, &mut statements);
    for expression in expressions {
        mentioned_names(expression, names);
    }
    for statement in statements {
        statement_mentioned_names(statement, names);
    }
}

/// The immediate subexpressions and substatements of one expression.
fn child_expressions<'a>(
    expression: &'a C0Expression,
    expressions: &mut Vec<&'a C0Expression>,
    statements: &mut Vec<&'a C0Statement>,
) {
    match expression {
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
        C0Expression::Call { arguments, .. } => expressions.extend(arguments.iter()),
        C0Expression::IndirectCall {
            function,
            arguments,
            ..
        } => {
            expressions.push(function);
            expressions.extend(arguments.iter());
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
        C0Expression::LessThan(left, right)
        | C0Expression::LessEqual(left, right)
        | C0Expression::GreaterThan(left, right)
        | C0Expression::GreaterEqual(left, right)
        | C0Expression::Equal(left, right)
        | C0Expression::NotEqual(left, right)
        | C0Expression::And(left, right)
        | C0Expression::Or(left, right)
        | C0Expression::Add(left, right)
        | C0Expression::Subtract(left, right)
        | C0Expression::Multiply(left, right)
        | C0Expression::Divide(left, right)
        | C0Expression::Remainder(left, right)
        | C0Expression::ShiftLeft(left, right)
        | C0Expression::ShiftRight(left, right)
        | C0Expression::BitwiseAnd(left, right)
        | C0Expression::BitwiseOr(left, right)
        | C0Expression::BitwiseXor(left, right)
        | C0Expression::Index(left, right) => {
            expressions.push(left);
            expressions.push(right);
        }
    }
}

/// The immediate subexpressions and substatements of one statement.
fn child_statements<'a>(
    statement: &'a C0Statement,
    expressions: &mut Vec<&'a C0Expression>,
    statements: &mut Vec<&'a C0Statement>,
) {
    match statement {
        C0Statement::Skip
        | C0Statement::Break
        | C0Statement::Continue
        | C0Statement::Goto { .. }
        | C0Statement::Declare { .. }
        | C0Statement::DeclareStructValue { .. } => {}
        C0Statement::Label { statement, .. } => statements.push(statement),
        C0Statement::Assign { expression, .. } => expressions.push(expression),
        C0Statement::CallAssign { arguments, .. } | C0Statement::Call { arguments, .. } => {
            expressions.extend(arguments.iter());
        }
        C0Statement::IndirectCall {
            function,
            arguments,
            ..
        } => {
            expressions.push(function);
            expressions.extend(arguments.iter());
        }
        C0Statement::HeapAllocate { bytes, .. } => expressions.push(bytes),
        C0Statement::HeapFree { pointer } => expressions.push(pointer),
        C0Statement::Assert { condition, .. } => expressions.push(condition),
        C0Statement::Seq(first, second) => {
            statements.push(first);
            statements.push(second);
        }
        C0Statement::Return(value) => expressions.push(value),
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
        } => {
            expressions.push(condition);
            statements.push(then_branch);
            statements.push(else_branch);
        }
        C0Statement::While { condition, body } | C0Statement::DoWhile { condition, body } => {
            expressions.push(condition);
            statements.push(body);
        }
        C0Statement::For {
            initializer,
            condition,
            step,
            body,
        } => {
            statements.push(initializer);
            expressions.push(condition);
            statements.push(step);
            statements.push(body);
        }
        C0Statement::Switch { expression, cases } => {
            expressions.push(expression);
            statements.extend(cases.iter().map(C0SwitchCase::body));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn summary(source: &str) -> AddressTakenSummary {
        let functions = super::super::syntax::parse_functions_for_source(source, "address.c")
            .expect("the fixture parses");
        summarize_address_taken(&functions)
    }

    #[test]
    fn a_scalar_local_whose_address_is_never_taken_is_reported() {
        let summary = summary("int32 f(void) { int32 x; int32* q; x = 5; return x; }\n");
        let never = summary.never_taken();
        assert!(never.contains("x"), "{never:?}");
        assert!(never.contains("q"), "{never:?}");
    }

    #[test]
    fn every_way_to_form_an_address_refuses_the_name() {
        let call = summary(
            "int32* echo(int32* p) { return p; }\nvoid f(void) { int32 x; int32* q; x = 5; q = echo(&x); x = 1; }\n",
        );
        assert!(!call.never_taken().contains("x"), "{:?}", call.taken());
        let indexed =
            summary("void f(void) { int32 a[4]; int32 i; int32* p; i = 0; p = &a[i]; }\n");
        assert!(!indexed.never_taken().contains("a"));
        assert!(!indexed.never_taken().contains("i"));
        let field = summary(
            "struct pair { int32 first; };\nvoid f(void) { struct pair s; int32* p; s.first = 1; p = &s.first; }\n",
        );
        assert!(!field.never_taken().contains("s"));
    }

    /// An address does not have to come back from the call it was handed to.
    /// `stash` parks it in storage and `fetch` hands it back later, so nothing
    /// connects the pointer `v` reads through to the `&x` it wrote. The pass
    /// answers about the `&`, not about where the address went, so the name is
    /// refused all the same.
    #[test]
    fn an_address_parked_in_storage_is_still_an_address() {
        let summary = summary(
            "void stash(int32** slot, int32* p) { *slot = p; }\nint32* fetch(int32** slot) { return *slot; }\nvoid v(int32** slot) { int32 x; int32* q; x = 5; stash(slot, &x); q = fetch(slot); x = 1; }\n",
        );
        assert!(
            !summary.never_taken().contains("x"),
            "the address escaped into `*slot`: {:?}",
            summary.never_taken()
        );
    }

    #[test]
    fn a_name_taken_in_another_function_is_refused_everywhere() {
        let summary = summary(
            "int32* echo(int32* p) { return p; }\nvoid taker(void) { int32 x; int32* q; q = echo(&x); }\nint32 innocent(void) { int32 x; x = 5; return x; }\n",
        );
        assert!(
            !summary.never_taken().contains("x"),
            "one name, one answer for the whole session: {:?}",
            summary.never_taken()
        );
    }
}
