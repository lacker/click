//! Temporary oracle: the recursive measure-read collection that `walk_spec`
//! replaced, compared with the walk on generated trees.

use super::*;
use crate::kernel::spec::walk::generated::Gen;

fn old_collect_pure_function_arguments(
    arguments: &[SpecPureFunctionArgument],
    reads: &mut MeasureReads,
) -> Result<(), UncollectedForm> {
    for argument in arguments {
        match argument {
            SpecPureFunctionArgument::Value(value) => {
                old_collect_spec_expression_c_variables(value, reads)?
            }
            SpecPureFunctionArgument::ArrayRef { pointer, .. } => {
                reads.memory = true;
                old_collect_spec_expression_c_variables(pointer, reads)?
            }
            SpecPureFunctionArgument::Integer(value) => {
                old_collect_spec_integer_expression_c_variables(value, reads)?
            }
            SpecPureFunctionArgument::Algebraic(value) => {
                old_collect_spec_algebraic_expression_c_variables(value, reads)?
            }
        }
    }
    Ok(())
}

fn old_collect_spec_algebraic_expression_c_variables(
    expression: &SpecAlgebraicExpression,
    reads: &mut MeasureReads,
) -> Result<(), UncollectedForm> {
    charge_termination_work(1);
    match &expression.node {
        SpecAlgebraicExpressionNode::Variable(_) | SpecAlgebraicExpressionNode::Binding(_) => {
            Ok(())
        }
        SpecAlgebraicExpressionNode::ResourceField(_) => {
            reads.model = true;
            Ok(())
        }
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            for field in fields {
                match field {
                    SpecAlgebraicValue::C(value) => {
                        old_collect_spec_expression_c_variables(value, reads)?
                    }
                    SpecAlgebraicValue::Integer(value) => {
                        old_collect_spec_integer_expression_c_variables(value, reads)?
                    }
                    SpecAlgebraicValue::Algebraic(value) => {
                        old_collect_spec_algebraic_expression_c_variables(value, reads)?
                    }
                }
            }
            Ok(())
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            old_collect_spec_algebraic_expression_c_variables(scrutinee, reads)?;
            for arm in arms {
                old_collect_spec_algebraic_expression_c_variables(&arm.body, reads)?;
            }
            Ok(())
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => {
            old_collect_pure_function_arguments(arguments, reads)
        }
    }
}

fn old_collect_spec_integer_expression_c_variables(
    expression: &SpecIntegerExpression,
    reads: &mut MeasureReads,
) -> Result<(), UncollectedForm> {
    charge_termination_work(1);
    match expression {
        SpecIntegerExpression::Term(_) => Ok(()),
        // A resource field reads the binder's instance, not a C local.
        SpecIntegerExpression::ResourceField(_) => Ok(()),
        SpecIntegerExpression::FromMachine(value) => {
            old_collect_spec_expression_c_variables(value, reads)
        }
        SpecIntegerExpression::Negate(inner) => {
            old_collect_spec_integer_expression_c_variables(inner, reads)
        }
        crate::kernel::binary_spec_integer_expression!(left, right) => {
            old_collect_spec_integer_expression_c_variables(left, reads)?;
            old_collect_spec_integer_expression_c_variables(right, reads)
        }
        SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
            old_collect_pure_function_arguments(arguments, reads)
        }
        SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
            old_collect_spec_algebraic_expression_c_variables(scrutinee, reads)?;
            for arm in arms {
                old_collect_spec_integer_expression_c_variables(&arm.body, reads)?;
            }
            Ok(())
        }
        SpecIntegerExpression::RangeFold { .. } => Err("a range fold"),
    }
}

fn old_collect_spec_expression_c_variables(
    expression: &SpecExpression,
    reads: &mut MeasureReads,
) -> Result<(), UncollectedForm> {
    charge_termination_work(1);
    match expression {
        SpecExpression::Value(_) => Ok(()),
        SpecExpression::CExpression(expression) => {
            collect_c_expression_variables(expression, &mut reads.variables);
            Ok(())
        }
        crate::kernel::binary_spec_expression!(left, right)
        | SpecExpression::PointerOffset {
            pointer: left,
            elements: right,
            ..
        } => {
            old_collect_spec_expression_c_variables(left, reads)?;
            old_collect_spec_expression_c_variables(right, reads)
        }
        SpecExpression::BitwiseNot(value) | SpecExpression::Cast(value, _) => {
            old_collect_spec_expression_c_variables(value, reads)
        }
        SpecExpression::MemoryLoad { pointer, .. } => {
            reads.memory = true;
            old_collect_spec_expression_c_variables(pointer, reads)
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => {
            old_collect_pure_function_arguments(arguments, reads)
        }
        SpecExpression::IntegerToMachine { value, .. } => {
            old_collect_spec_integer_expression_c_variables(value, reads)
        }
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            old_collect_spec_algebraic_expression_c_variables(scrutinee, reads)?;
            for arm in arms {
                old_collect_spec_expression_c_variables(&arm.body, reads)?;
            }
            Ok(())
        }
        // A resource field reads the binder's instance, not a C local.
        SpecExpression::ResourceField { .. } => Ok(()),
        SpecExpression::CountedResourceCount { .. } => Err("a counted-resource count"),
        SpecExpression::If { .. } => Err("a conditional `if` expression"),
        SpecExpression::RangeFold { .. } => Err("a range fold"),
        SpecExpression::Let { .. } => Err("a `let` expression"),
        SpecExpression::LoopEntrySnapshot(_) => Err("a loop-entry snapshot"),
        SpecExpression::AggregateFieldValue { .. } => Err("a by-value aggregate field"),
    }
}

fn same(
    new: Result<(), UncollectedForm>,
    new_reads: &MeasureReads,
    old: Result<(), UncollectedForm>,
    old_reads: &MeasureReads,
) -> bool {
    new == old
        && (old.is_err()
            || (new_reads.variables == old_reads.variables
                && new_reads.memory == old_reads.memory
                && new_reads.model == old_reads.model))
}

#[test]
fn measure_reads_agree_with_their_recursive_original() {
    let mut generator = Gen::new(0x2545_f491_4f6c_dd1d);
    let mut collected = 0;
    for round in 0..4000 {
        let depth = 1 + (round % 4) as u32;
        let expression = generator.expr(depth);
        let (mut old_reads, mut new_reads) = (MeasureReads::default(), MeasureReads::default());
        let old = old_collect_spec_expression_c_variables(&expression, &mut old_reads);
        let new = collect_spec_c_variables(SpecNode::Expression(&expression), &mut new_reads);
        assert!(same(new, &new_reads, old, &old_reads), "{expression:?}");
        collected += usize::from(old.is_ok());
        let integer = generator.int(depth);
        let (mut old_reads, mut new_reads) = (MeasureReads::default(), MeasureReads::default());
        let old = old_collect_spec_integer_expression_c_variables(&integer, &mut old_reads);
        let new = collect_spec_c_variables(SpecNode::Integer(&integer), &mut new_reads);
        assert!(same(new, &new_reads, old, &old_reads), "{integer:?}");
        collected += usize::from(old.is_ok());
    }
    // Both collected and refused answers occur often enough to mean something.
    assert!((400..7600).contains(&collected), "{collected}");
}
