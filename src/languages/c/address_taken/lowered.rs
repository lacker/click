//! Addressability of imported executable bodies, including generated captures.
//! Walk the actual typed body. An opaque non-null pointer literal disables the
//! summary: unlike source address expressions, it can name arbitrary storage.

use super::AddressTakenSummary;
use crate::kernel::{CExpression, CFunction, CStatement, CType, CValue};

fn declare(summary: &mut AddressTakenSummary, name: &str, ty: CType) {
    if ty.is_pointer()
        || matches!(
            ty,
            CType::Bool
                | CType::Int8
                | CType::UInt8
                | CType::Int16
                | CType::UInt16
                | CType::Int32
                | CType::UInt32
                | CType::Int64
                | CType::UInt64
                | CType::Float32
                | CType::Float64
        )
    {
        summary.scalar_declarations.insert(name.to_owned());
    } else {
        summary.taken.insert(name.to_owned());
    }
}

pub(super) fn summarize(function: &CFunction, summary: &mut AddressTakenSummary) -> bool {
    for parameter in function.parameters() {
        crate::instrumentation::record_deterministic_work(1);
        if parameter.aggregate_layout().is_some() {
            summary.taken.insert(parameter.name().to_owned());
        } else {
            declare(summary, parameter.name(), parameter.c_type());
        }
    }
    let mut statements = vec![function.body()];
    let mut expressions = Vec::new();
    while let Some(statement) = statements.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match statement {
            CStatement::Declare {
                name,
                c_type,
                initializer,
                ..
            } => {
                declare(summary, name, *c_type);
                expressions.extend(initializer.iter().map(|expression| (expression, false)));
            }
            CStatement::DeclareAggregate { name, .. } => {
                summary.taken.insert(name.clone());
            }
            CStatement::Skip
            | CStatement::Break
            | CStatement::Continue
            | CStatement::Goto { .. }
            | CStatement::EndAutomaticLifetimes { .. } => {}
            CStatement::Assign { expression, .. }
            | CStatement::Return(expression)
            | CStatement::Throw(expression)
            | CStatement::Switch { expression, .. } => {
                expressions.push((expression, false));
                if let CStatement::Switch { cases, .. } = statement {
                    statements.extend(cases.iter().map(|case| case.body.as_ref()));
                }
            }
            CStatement::Call { arguments, .. } | CStatement::CallAssign { arguments, .. } => {
                expressions.extend(arguments.iter().map(|argument| (argument, false)));
            }
            CStatement::HeapAllocate { bytes, .. } => expressions.push((bytes, false)),
            CStatement::HeapFree { pointer } => expressions.push((pointer, false)),
            CStatement::Assert { condition, .. } => expressions.push((condition, false)),
            CStatement::Store { pointer, value }
            | CStatement::TypedStore { pointer, value, .. } => {
                expressions.extend([(pointer, false), (value, false)]);
            }
            CStatement::CopyAggregate { target, source, .. }
            | CStatement::InitializeScalarArray { target, source, .. }
            | CStatement::Update {
                target,
                operand: source,
                ..
            } => {
                expressions.extend([(target, false), (source, false)]);
            }
            CStatement::Seq(first, second) => statements.extend([first.as_ref(), second.as_ref()]),
            CStatement::TryCatchInt32 {
                try_body,
                binding,
                handler,
                ..
            } => {
                declare(summary, binding, CType::Int32);
                statements.extend([try_body.as_ref(), handler.as_ref()]);
            }
            CStatement::If {
                condition,
                then_branch,
                else_branch,
            } => {
                expressions.push((condition, false));
                statements.extend([then_branch.as_ref(), else_branch.as_ref()]);
            }
            CStatement::While {
                condition, body, ..
            } => {
                expressions.push((condition, false));
                statements.push(body);
            }
            CStatement::ForStep { step, .. } | CStatement::Scope { body: step } => {
                statements.push(step)
            }
        }
    }
    while let Some((expression, addressed)) = expressions.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match expression {
            CExpression::Value(value) => {
                if matches!(value, CValue::Pointer(pointer) if pointer.pointer() != &crate::kernel::Pointer::null())
                {
                    return false;
                }
            }
            CExpression::Variable(name) => {
                if addressed {
                    summary.taken.insert(name.clone());
                }
            }
            CExpression::FunctionAddress(_) => {}
            CExpression::MemberAddress { object: value, .. }
            | CExpression::AddressOf(value)
            | CExpression::CheckedObjectAddress(value) => {
                expressions.push((value, true));
            }
            CExpression::Cast {
                expression: value, ..
            }
            | CExpression::FloatNegate(value)
            | CExpression::FloatClassification {
                expression: value, ..
            }
            | CExpression::PointerOffsetBytes { pointer: value, .. }
            | CExpression::PointerAligned { pointer: value, .. }
            | CExpression::Not(value)
            | CExpression::BitwiseNot(value)
            | CExpression::Load(value)
            | CExpression::TypedLoad { pointer: value, .. } => expressions.push((value, addressed)),
            CExpression::Conditional {
                condition,
                then_branch,
                else_branch,
            } => {
                expressions.extend([
                    (condition.as_ref(), addressed),
                    (then_branch.as_ref(), addressed),
                    (else_branch.as_ref(), addressed),
                ]);
            }
            crate::kernel::binary_c_expression!(left, right) => {
                expressions.extend([(left.as_ref(), addressed), (right.as_ref(), addressed)]);
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use crate::kernel::*;
    use crate::languages::c::{
        address_taken::summarize_address_taken,
        syntax::{C0Function, C0Type},
    };

    fn imported(body: CStatement) -> C0Function {
        C0Function::external(C0Type::Void, "imported".into(), vec![])
            .with_prelowered_kernel_function(c_function(CType::Void, "imported", vec![], body))
    }

    // Imported bodies must participate in the same whole-program name rule as
    // C bodies, and array/aggregate names already expose their storage address.
    #[test]
    fn imported_addressability_tracks_captures_escapes_and_arrays() {
        let first = imported(c_seq(
            c_declare("capture", CType::Int32Pointer),
            c_seq(
                c_declare("escaped", CType::Int32),
                c_declare("array", CType::Int32Array(2)),
            ),
        ));
        let second = imported(c_call(
            "callee",
            vec![CExpression::AddressOf(Box::new(c_variable("escaped")))],
        ));
        let summary = summarize_address_taken([&first, &second]);
        assert!(summary.never_taken().contains("capture"));
        assert!(!summary.never_taken().contains("escaped"));
        assert!(!summary.never_taken().contains("array"));
    }

    #[test]
    fn opaque_imported_pointer_literals_disable_the_bundle_summary() {
        let function = imported(c_seq(
            c_declare("capture", CType::Int32),
            c_return(c_pointer_value(Pointer {
                block: "local:capture".into(),
                offset: PointerOffsetTerm::Constant(0),
            })),
        ));
        assert!(
            summarize_address_taken([&function])
                .never_taken()
                .is_empty()
        );
    }

    #[test]
    fn imported_addressability_work_scales_with_body_size() {
        for count in [16, 64, 256] {
            let mut body = c_skip();
            for index in 0..count {
                body = c_seq(
                    body,
                    c_declare(format!("capture_{index}"), CType::Int32Pointer),
                );
            }
            let function = imported(body);
            let (summary, work) = crate::instrumentation::measure_deterministic_work(|| {
                summarize_address_taken([&function])
            });
            assert_eq!(summary.never_taken().len(), count);
            assert_eq!(work, 2 * count + 1);
        }
    }
}
