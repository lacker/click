//! Temporary oracle: the recursive body-read check that `walk_spec` replaced,
//! compared with the walk on generated trees.

use super::*;
use crate::kernel::primitives::{
    SpecAlgebraicValue, SpecIntegerRangeFoldIndex, SpecPredicateArgument, SpecPureFunctionArgument,
};
use crate::kernel::spec::walk::generated::Gen;

fn old_collect_body_reads(
    expression: &SpecExpression,
    bound: &mut Vec<String>,
    reads: &mut BodyReads,
) -> Result<(), UninspectedForm> {
    match expression {
        // A resource field reads the binder's instance, not a C name.
        SpecExpression::Value(_) | SpecExpression::ResourceField { .. } => Ok(()),
        SpecExpression::CExpression(expression) => {
            collect_c_expression_reads(expression, bound, reads);
            Ok(())
        }
        SpecExpression::IntegerToMachine { value, .. } => {
            old_collect_integer_body_reads(value, bound, reads)
        }
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            old_collect_algebraic_body_reads(scrutinee, bound, reads)?;
            for arm in arms {
                with_bound(bound, arm.bindings.iter().cloned(), |bound| {
                    old_collect_body_reads(&arm.body, bound, reads)
                })?;
            }
            Ok(())
        }
        SpecExpression::CountedResourceCount { .. } => {
            Err(UninspectedForm("a counted-resource count"))
        }
        crate::kernel::binary_spec_expression!(left, right)
        | SpecExpression::PointerOffset {
            pointer: left,
            elements: right,
            ..
        } => {
            old_collect_body_reads(left, bound, reads)?;
            old_collect_body_reads(right, bound, reads)
        }
        SpecExpression::BitwiseNot(inner) | SpecExpression::Cast(inner, _) => {
            old_collect_body_reads(inner, bound, reads)
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            old_collect_proposition_body_reads(condition, bound, reads)?;
            old_collect_body_reads(then_branch, bound, reads)?;
            old_collect_body_reads(else_branch, bound, reads)
        }
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            old_collect_body_reads(start, bound, reads)?;
            old_collect_body_reads(end, bound, reads)?;
            old_collect_body_reads(initial, bound, reads)?;
            with_bound(bound, [accumulator.clone(), item.clone()], |bound| {
                old_collect_body_reads(body, bound, reads)
            })
        }
        SpecExpression::Let { name, value, body } => {
            old_collect_body_reads(value, bound, reads)?;
            with_bound(bound, [name.clone()], |bound| {
                old_collect_body_reads(body, bound, reads)
            })
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => {
            old_collect_argument_body_reads(arguments, bound, reads)
        }
        SpecExpression::LoopEntrySnapshot(_) => Err(UninspectedForm("a loop-entry snapshot")),
        SpecExpression::MemoryLoad { pointer, .. } => {
            reads.memory = true;
            old_collect_body_reads(pointer, bound, reads)
        }
        SpecExpression::AggregateFieldValue {
            parameter, pointer, ..
        } => {
            note_c_name(parameter, bound, reads);
            old_collect_body_reads(pointer, bound, reads)
        }
    }
}

fn old_collect_integer_body_reads(
    expression: &SpecIntegerExpression,
    bound: &mut Vec<String>,
    reads: &mut BodyReads,
) -> Result<(), UninspectedForm> {
    match expression {
        SpecIntegerExpression::ResourceField(_) | SpecIntegerExpression::Term(_) => Ok(()),
        SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
            old_collect_argument_body_reads(arguments, bound, reads)
        }
        SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
            old_collect_algebraic_body_reads(scrutinee, bound, reads)?;
            for arm in arms {
                with_bound(bound, arm.bindings.iter().cloned(), |bound| {
                    old_collect_integer_body_reads(&arm.body, bound, reads)
                })?;
            }
            Ok(())
        }
        SpecIntegerExpression::FromMachine(value) => old_collect_body_reads(value, bound, reads),
        SpecIntegerExpression::Negate(inner) => old_collect_integer_body_reads(inner, bound, reads),
        crate::kernel::binary_spec_integer_expression!(left, right) => {
            old_collect_integer_body_reads(left, bound, reads)?;
            old_collect_integer_body_reads(right, bound, reads)
        }
        // The fold's accumulator and item are variables, not names.
        SpecIntegerExpression::RangeFold {
            index,
            initial,
            body,
            ..
        } => {
            match index {
                SpecIntegerRangeFoldIndex::Int32 { start, end }
                | SpecIntegerRangeFoldIndex::UInt64 { start, end } => {
                    old_collect_body_reads(start, bound, reads)?;
                    old_collect_body_reads(end, bound, reads)?;
                }
                SpecIntegerRangeFoldIndex::Integer { start, end } => {
                    old_collect_integer_body_reads(start, bound, reads)?;
                    old_collect_integer_body_reads(end, bound, reads)?;
                }
            }
            old_collect_integer_body_reads(initial, bound, reads)?;
            old_collect_integer_body_reads(body, bound, reads)
        }
    }
}

fn old_collect_algebraic_body_reads(
    expression: &SpecAlgebraicExpression,
    bound: &mut Vec<String>,
    reads: &mut BodyReads,
) -> Result<(), UninspectedForm> {
    match &expression.node {
        // An algebraic binding is a parameter or a match binding of the
        // algebraic sort, never a C name.
        SpecAlgebraicExpressionNode::Variable(_)
        | SpecAlgebraicExpressionNode::Binding(_)
        | SpecAlgebraicExpressionNode::ResourceField(_) => Ok(()),
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            for field in fields {
                match field {
                    SpecAlgebraicValue::C(value) => old_collect_body_reads(value, bound, reads)?,
                    SpecAlgebraicValue::Integer(value) => {
                        old_collect_integer_body_reads(value, bound, reads)?
                    }
                    SpecAlgebraicValue::Algebraic(value) => {
                        old_collect_algebraic_body_reads(value, bound, reads)?
                    }
                }
            }
            Ok(())
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            old_collect_algebraic_body_reads(scrutinee, bound, reads)?;
            for arm in arms {
                with_bound(bound, arm.bindings.iter().cloned(), |bound| {
                    old_collect_algebraic_body_reads(&arm.body, bound, reads)
                })?;
            }
            Ok(())
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => {
            old_collect_argument_body_reads(arguments, bound, reads)
        }
    }
}

fn old_collect_argument_body_reads(
    arguments: &[SpecPureFunctionArgument],
    bound: &mut Vec<String>,
    reads: &mut BodyReads,
) -> Result<(), UninspectedForm> {
    for argument in arguments {
        match argument {
            // An array reference carries its own snapshot as an argument;
            // only the pointer expression is a read of this body's scope.
            SpecPureFunctionArgument::Value(value)
            | SpecPureFunctionArgument::ArrayRef { pointer: value, .. } => {
                old_collect_body_reads(value, bound, reads)?
            }
            SpecPureFunctionArgument::Integer(value) => {
                old_collect_integer_body_reads(value, bound, reads)?
            }
            SpecPureFunctionArgument::Algebraic(value) => {
                old_collect_algebraic_body_reads(value, bound, reads)?
            }
        }
    }
    Ok(())
}

fn old_collect_proposition_body_reads(
    proposition: &SpecProposition,
    bound: &mut Vec<String>,
    reads: &mut BodyReads,
) -> Result<(), UninspectedForm> {
    match proposition {
        SpecProposition::Comparison { left, right, .. } => {
            old_collect_body_reads(left, bound, reads)?;
            old_collect_body_reads(right, bound, reads)
        }
        SpecProposition::IntegerComparison { left, right, .. } => {
            old_collect_integer_body_reads(left, bound, reads)?;
            old_collect_integer_body_reads(right, bound, reads)
        }
        SpecProposition::AlgebraicComparison { left, right, .. } => {
            old_collect_algebraic_body_reads(left, bound, reads)?;
            old_collect_algebraic_body_reads(right, bound, reads)
        }
        SpecProposition::FloatClassification { expression, .. }
        | SpecProposition::Defined(expression) => old_collect_body_reads(expression, bound, reads),
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            old_collect_proposition_body_reads(left, bound, reads)?;
            old_collect_proposition_body_reads(right, bound, reads)
        }
        SpecProposition::Not(body) => old_collect_proposition_body_reads(body, bound, reads),
        SpecProposition::Predicate { arguments, .. } => {
            for argument in arguments {
                match argument {
                    SpecPredicateArgument::Value(value)
                    | SpecPredicateArgument::ArrayRef { pointer: value, .. } => {
                        old_collect_body_reads(value, bound, reads)?
                    }
                }
            }
            Ok(())
        }
        // Quantifiers, sequences, resources and loadability do not occur in
        // a memory-independent body; a body that has one is not inspected.
        _ => Err(UninspectedForm(
            "a proposition form the closedness check does not inspect",
        )),
    }
}

#[test]
fn body_reads_agree_with_their_recursive_original() {
    let mut generator = Gen::new(0x3c6e_f372_fe94_f82b);
    let (mut inspected, mut free) = (0, 0);
    for round in 0..4000 {
        let depth = 1 + (round % 4) as u32;
        let expression = generator.expr(depth);
        let (mut old_bound, mut new_bound) = (vec!["p".to_string()], vec!["p".to_string()]);
        let (mut old_reads, mut new_reads) = (BodyReads::default(), BodyReads::default());
        let old = old_collect_body_reads(&expression, &mut old_bound, &mut old_reads);
        let new = collect_body_reads(
            SpecNode::Expression(&expression),
            &mut new_bound,
            &mut new_reads,
        );
        assert_eq!(
            new.err().map(|form| form.0),
            old.as_ref().err().map(|form| form.0)
        );
        assert_eq!(new_bound, old_bound);
        if old.is_ok() {
            assert_eq!(
                new_reads.free_c_names, old_reads.free_c_names,
                "{expression:?}"
            );
            assert_eq!(new_reads.memory, old_reads.memory, "{expression:?}");
            inspected += 1;
            free += usize::from(!old_reads.free_c_names.is_empty());
        }
    }
    // Inspected bodies, with and without free names, occur often enough to
    // mean something.
    assert!((400..3600).contains(&inspected), "{inspected} {free}");
    assert!((200..inspected - 100).contains(&free), "{inspected} {free}");
}
