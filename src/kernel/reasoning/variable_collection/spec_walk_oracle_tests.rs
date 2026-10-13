//! Temporary oracle: the recursive spec collectors that `walk_spec` replaced,
//! compared with the walks on generated trees.

use super::*;
use crate::kernel::spec::walk::generated::Gen;

fn old_collect_spec_memory_bitvector_variables(
    _memory: &SpecMemory,
    _variables: &mut BTreeSet<Variable>,
) {
    // A specification memory is an execution snapshot. Its blocks and cells
    // are opaque to lexical variable collection; callers still visit the
    // explicit pointer and expression payloads adjacent to this snapshot.
}

fn old_collect_spec_expression_bitvector_variables(
    expression: &SpecExpression,
    variables: &mut BTreeSet<Variable>,
) {
    match expression {
        SpecExpression::ResourceField { .. } => {}
        SpecExpression::IntegerToMachine { value, .. } => {
            old_collect_spec_integer_variables(value, variables);
        }
        SpecExpression::Value(value) => collect_c_value_bitvector_variables(value, variables),
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            old_collect_spec_algebraic_expression_bitvector_variables(scrutinee, variables);
            for arm in arms {
                old_collect_spec_expression_bitvector_variables(&arm.body, variables);
            }
        }
        SpecExpression::CExpression(expression) => {
            collect_c_expression_bitvector_variables(expression, variables);
        }
        SpecExpression::CountedResourceCount { arguments, .. } => {
            for argument in arguments.iter().flatten() {
                old_collect_spec_expression_bitvector_variables(argument, variables);
            }
        }
        crate::kernel::binary_spec_expression!(left, right) => {
            old_collect_spec_expression_bitvector_variables(left, variables);
            old_collect_spec_expression_bitvector_variables(right, variables);
        }
        SpecExpression::BitwiseNot(expression) | SpecExpression::Cast(expression, _) => {
            old_collect_spec_expression_bitvector_variables(expression, variables);
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            old_collect_spec_proposition_bitvector_variables(condition, variables);
            old_collect_spec_expression_bitvector_variables(then_branch, variables);
            old_collect_spec_expression_bitvector_variables(else_branch, variables);
        }
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            accumulator: _,
            item: _,
            body,
        } => {
            old_collect_spec_expression_bitvector_variables(start, variables);
            old_collect_spec_expression_bitvector_variables(end, variables);
            old_collect_spec_expression_bitvector_variables(initial, variables);
            old_collect_spec_expression_bitvector_variables(body, variables);
        }
        SpecExpression::Let {
            name: _,
            value,
            body,
        } => {
            old_collect_spec_expression_bitvector_variables(value, variables);
            old_collect_spec_expression_bitvector_variables(body, variables);
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                old_collect_spec_function_argument_bitvector_variables(argument, variables);
            }
        }
        SpecExpression::LoopEntrySnapshot(expression) => {
            old_collect_spec_expression_bitvector_variables(expression, variables);
        }
        SpecExpression::PointerOffset {
            pointer,
            elements,
            byte_width: _,
        } => {
            old_collect_spec_expression_bitvector_variables(pointer, variables);
            old_collect_spec_expression_bitvector_variables(elements, variables);
        }
        SpecExpression::AggregateFieldValue { pointer, .. } => {
            old_collect_spec_expression_bitvector_variables(pointer, variables);
        }
        SpecExpression::MemoryLoad {
            memory, pointer, ..
        } => {
            old_collect_spec_memory_bitvector_variables(memory, variables);
            old_collect_spec_expression_bitvector_variables(pointer, variables);
        }
    }
}

fn old_collect_spec_proposition_bitvector_variables(
    proposition: &SpecProposition,
    variables: &mut BTreeSet<Variable>,
) {
    match proposition {
        SpecProposition::IntegerComparison { left, right, .. } => {
            old_collect_spec_integer_variables(left, variables);
            old_collect_spec_integer_variables(right, variables);
        }
        SpecProposition::AlgebraicComparison { left, right, .. } => {
            old_collect_spec_algebraic_expression_bitvector_variables(left, variables);
            old_collect_spec_algebraic_expression_bitvector_variables(right, variables);
        }
        SpecProposition::SequenceMembership { element, sequence } => {
            old_collect_spec_expression_bitvector_variables(element, variables);
            old_collect_spec_sequence_bitvector_variables(sequence, variables);
        }
        SpecProposition::SequenceComparison { left, right, .. } => {
            old_collect_spec_sequence_bitvector_variables(left, variables);
            old_collect_spec_sequence_bitvector_variables(right, variables);
        }
        SpecProposition::Comparison { left, right, .. } => {
            old_collect_spec_expression_bitvector_variables(left, variables);
            old_collect_spec_expression_bitvector_variables(right, variables);
        }
        SpecProposition::FloatClassification { expression, .. } => {
            old_collect_spec_expression_bitvector_variables(expression, variables);
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            old_collect_spec_proposition_bitvector_variables(left, variables);
            old_collect_spec_proposition_bitvector_variables(right, variables);
        }
        SpecProposition::Not(body) => {
            old_collect_spec_proposition_bitvector_variables(body, variables);
        }
        SpecProposition::ForAllMachineInteger { variable, body, .. }
        | SpecProposition::ForAllInt32 { variable, body, .. }
        | SpecProposition::ForAllInteger { variable, body, .. }
        | SpecProposition::ForAllAlgebraic { variable, body, .. }
        | SpecProposition::ForAllPointer { variable, body, .. }
        | SpecProposition::ExistsMachineInteger { variable, body, .. }
        | SpecProposition::ExistsInt32 { variable, body, .. }
        | SpecProposition::ExistsInteger { variable, body, .. }
        | SpecProposition::ExistsAlgebraic { variable, body, .. }
        | SpecProposition::ExistsPointer { variable, body, .. } => {
            old_collect_spec_proposition_bitvector_variables(body, variables);
            variables.remove(variable);
        }
        SpecProposition::Predicate { arguments, .. } => {
            for argument in arguments {
                match argument {
                    SpecPredicateArgument::Value(expression) => {
                        old_collect_spec_expression_bitvector_variables(expression, variables);
                    }
                    SpecPredicateArgument::ArrayRef { pointer, .. } => {
                        old_collect_spec_expression_bitvector_variables(pointer, variables);
                    }
                }
            }
        }
        SpecProposition::ResourceSeparate { left, right }
        | SpecProposition::ResourceContains {
            parent: left,
            child: right,
        } => {
            old_collect_spec_resource_bitvector_variables(left, variables);
            old_collect_spec_resource_bitvector_variables(right, variables);
        }
        SpecProposition::MemoryInitialized { memory, base, .. } => {
            old_collect_spec_memory_bitvector_variables(memory, variables);
            old_collect_spec_expression_bitvector_variables(base, variables);
        }
        SpecProposition::ValidPlace {
            memory,
            pointer: base,
            range,
            ..
        } => {
            old_collect_spec_memory_bitvector_variables(memory, variables);
            old_collect_spec_expression_bitvector_variables(base, variables);
            if let Some((start, end)) = range {
                old_collect_spec_expression_bitvector_variables(start, variables);
                old_collect_spec_expression_bitvector_variables(end, variables);
            }
        }
        SpecProposition::MemoryLoadable {
            memory,
            base,
            start,
            end,
            ..
        } => {
            old_collect_spec_memory_bitvector_variables(memory, variables);
            old_collect_spec_expression_bitvector_variables(base, variables);
            old_collect_spec_expression_bitvector_variables(start, variables);
            old_collect_spec_expression_bitvector_variables(end, variables);
        }
        SpecProposition::Defined(expression) => {
            old_collect_spec_expression_bitvector_variables(expression, variables);
        }
    }
}

fn old_collect_spec_integer_variables(
    expression: &SpecIntegerExpression,
    variables: &mut BTreeSet<Variable>,
) {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        match expression {
            SpecIntegerExpression::ResourceField(_) => {}
            SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
                old_collect_spec_algebraic_expression_bitvector_variables(scrutinee, variables);
                for arm in arms {
                    old_collect_spec_integer_variables(&arm.body, variables);
                }
            }
            SpecIntegerExpression::Term(term) => collect_integer_variables(term, variables),
            SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
                for argument in arguments {
                    match argument {
                        SpecPureFunctionArgument::Value(value) => {
                            old_collect_spec_expression_bitvector_variables(value, variables)
                        }
                        SpecPureFunctionArgument::Integer(value) => {
                            old_collect_spec_integer_variables(value, variables)
                        }
                        SpecPureFunctionArgument::Algebraic(value) => {
                            old_collect_spec_algebraic_expression_bitvector_variables(
                                value, variables,
                            )
                        }
                        SpecPureFunctionArgument::ArrayRef { pointer, .. } => {
                            old_collect_spec_expression_bitvector_variables(pointer, variables)
                        }
                    }
                }
            }
            SpecIntegerExpression::FromMachine(value) => {
                old_collect_spec_expression_bitvector_variables(value, variables)
            }
            SpecIntegerExpression::Negate(inner) => pending.push(inner),
            crate::kernel::binary_spec_integer_expression!(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            SpecIntegerExpression::RangeFold {
                index,
                initial,
                body,
                ..
            } => {
                match index {
                    SpecIntegerRangeFoldIndex::Int32 { start, end }
                    | SpecIntegerRangeFoldIndex::UInt64 { start, end } => {
                        old_collect_spec_expression_bitvector_variables(start, variables);
                        old_collect_spec_expression_bitvector_variables(end, variables);
                    }
                    SpecIntegerRangeFoldIndex::Integer { start, end } => {
                        pending.push(start);
                        pending.push(end);
                    }
                }
                pending.push(initial);
                pending.push(body);
            }
        }
    }
}

fn old_collect_spec_integer_bound_variables(
    expression: &SpecIntegerExpression,
    variables: &mut BTreeSet<Variable>,
) {
    old_collect_spec_integer_variables(expression, variables);
    let mut integer_seen = SeenTerms::default();
    old_collect_spec_integer_bound_variables_inner(expression, variables, &mut integer_seen);
}

fn old_collect_spec_integer_bound_variables_inner(
    expression: &SpecIntegerExpression,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    match expression {
        SpecIntegerExpression::ResourceField(projection) => {
            variables.insert(projection.identity);
        }
        SpecIntegerExpression::Term(term) => {
            collect_integer_bound_identities(term, variables, integer_seen);
        }
        SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
            old_collect_spec_algebraic_bound_identities(scrutinee, variables, integer_seen);
            for arm in arms {
                for variable in arm.binding_variables.iter().flatten() {
                    variables.insert(*variable);
                }
                old_collect_spec_integer_bound_variables_inner(&arm.body, variables, integer_seen);
            }
        }
        SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                old_collect_spec_integer_bound_argument(argument, variables, integer_seen);
            }
        }
        SpecIntegerExpression::FromMachine(expression) => {
            old_collect_spec_integer_bound_expression(expression, variables, integer_seen);
        }
        SpecIntegerExpression::Negate(value) => {
            old_collect_spec_integer_bound_variables_inner(value, variables, integer_seen);
        }
        crate::kernel::binary_spec_integer_expression!(left, right) => {
            old_collect_spec_integer_bound_variables_inner(left, variables, integer_seen);
            old_collect_spec_integer_bound_variables_inner(right, variables, integer_seen);
        }
        SpecIntegerExpression::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            variables.insert(*accumulator);
            variables.insert(*item);
            match index {
                SpecIntegerRangeFoldIndex::Int32 { start, end }
                | SpecIntegerRangeFoldIndex::UInt64 { start, end } => {
                    old_collect_spec_integer_bound_expression(start, variables, integer_seen);
                    old_collect_spec_integer_bound_expression(end, variables, integer_seen);
                }
                SpecIntegerRangeFoldIndex::Integer { start, end } => {
                    old_collect_spec_integer_bound_variables_inner(start, variables, integer_seen);
                    old_collect_spec_integer_bound_variables_inner(end, variables, integer_seen);
                }
            }
            old_collect_spec_integer_bound_variables_inner(initial, variables, integer_seen);
            old_collect_spec_integer_bound_variables_inner(body, variables, integer_seen);
        }
    }
}

fn old_collect_spec_integer_bound_argument(
    argument: &SpecPureFunctionArgument,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    match argument {
        SpecPureFunctionArgument::Value(value) => {
            old_collect_spec_integer_bound_expression(value, variables, integer_seen);
        }
        SpecPureFunctionArgument::Integer(value) => {
            old_collect_spec_integer_bound_variables_inner(value, variables, integer_seen);
        }
        SpecPureFunctionArgument::Algebraic(value) => {
            old_collect_spec_algebraic_bound_identities(value, variables, integer_seen);
        }
        SpecPureFunctionArgument::ArrayRef {
            memory, pointer, ..
        } => {
            old_collect_spec_memory_bound_identities(memory, variables, integer_seen);
            old_collect_spec_integer_bound_expression(pointer, variables, integer_seen);
        }
    }
}

fn old_collect_spec_integer_bound_expression(
    expression: &SpecExpression,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    match expression {
        SpecExpression::Value(value) => {
            collect_c_value_bound_identities(value, variables, integer_seen);
        }
        SpecExpression::IntegerToMachine { value, .. } => {
            old_collect_spec_integer_bound_variables_inner(value, variables, integer_seen);
        }
        SpecExpression::ResourceField { projection, .. } => {
            variables.insert(projection.identity);
        }
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            old_collect_spec_algebraic_bound_identities(scrutinee, variables, integer_seen);
            for arm in arms {
                old_collect_spec_integer_bound_expression(&arm.body, variables, integer_seen);
            }
        }
        SpecExpression::CExpression(expression) => {
            collect_c_expression_bound_identities(expression, variables, integer_seen);
        }
        SpecExpression::CountedResourceCount { arguments, .. } => {
            for argument in arguments.iter().flatten() {
                old_collect_spec_integer_bound_expression(argument, variables, integer_seen);
            }
        }
        crate::kernel::binary_spec_expression!(left, right) => {
            old_collect_spec_integer_bound_expression(left, variables, integer_seen);
            old_collect_spec_integer_bound_expression(right, variables, integer_seen);
        }
        SpecExpression::BitwiseNot(expression)
        | SpecExpression::Cast(expression, _)
        | SpecExpression::LoopEntrySnapshot(expression) => {
            old_collect_spec_integer_bound_expression(expression, variables, integer_seen);
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            old_collect_spec_proposition_bound_identities(condition, variables, integer_seen);
            old_collect_spec_integer_bound_expression(then_branch, variables, integer_seen);
            old_collect_spec_integer_bound_expression(else_branch, variables, integer_seen);
        }
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            old_collect_spec_integer_bound_expression(start, variables, integer_seen);
            old_collect_spec_integer_bound_expression(end, variables, integer_seen);
            old_collect_spec_integer_bound_expression(initial, variables, integer_seen);
            old_collect_spec_integer_bound_expression(body, variables, integer_seen);
        }
        SpecExpression::Let { value, body, .. } => {
            old_collect_spec_integer_bound_expression(value, variables, integer_seen);
            old_collect_spec_integer_bound_expression(body, variables, integer_seen);
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                old_collect_spec_integer_bound_argument(argument, variables, integer_seen);
            }
        }
        SpecExpression::PointerOffset {
            pointer, elements, ..
        } => {
            old_collect_spec_integer_bound_expression(pointer, variables, integer_seen);
            old_collect_spec_integer_bound_expression(elements, variables, integer_seen);
        }
        SpecExpression::AggregateFieldValue { pointer, .. } => {
            old_collect_spec_integer_bound_expression(pointer, variables, integer_seen);
        }
        SpecExpression::MemoryLoad {
            memory, pointer, ..
        } => {
            old_collect_spec_memory_bound_identities(memory, variables, integer_seen);
            old_collect_spec_integer_bound_expression(pointer, variables, integer_seen);
        }
    }
}

fn old_collect_spec_algebraic_bound_identities(
    expression: &SpecAlgebraicExpression,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    match &expression.node {
        SpecAlgebraicExpressionNode::Variable(variable) => {
            variables.insert(*variable);
        }
        SpecAlgebraicExpressionNode::Binding(_) | SpecAlgebraicExpressionNode::ResourceField(_) => {
        }
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            for field in fields {
                match field {
                    SpecAlgebraicValue::C(value) => {
                        old_collect_spec_integer_bound_expression(value, variables, integer_seen);
                    }
                    SpecAlgebraicValue::Integer(value) => {
                        old_collect_spec_integer_bound_variables_inner(
                            value,
                            variables,
                            integer_seen,
                        );
                    }
                    SpecAlgebraicValue::Algebraic(value) => {
                        old_collect_spec_algebraic_bound_identities(value, variables, integer_seen);
                    }
                }
            }
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            old_collect_spec_algebraic_bound_identities(scrutinee, variables, integer_seen);
            for arm in arms {
                old_collect_spec_algebraic_bound_identities(&arm.body, variables, integer_seen);
            }
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                old_collect_spec_integer_bound_argument(argument, variables, integer_seen);
            }
        }
    }
}

fn old_collect_spec_sequence_bound_identities(
    sequence: &SpecSequenceExpression,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    match sequence {
        SpecSequenceExpression::Literal(values) => {
            for value in values {
                old_collect_spec_integer_bound_expression(value, variables, integer_seen);
            }
        }
        SpecSequenceExpression::Concat(left, right) => {
            old_collect_spec_sequence_bound_identities(left, variables, integer_seen);
            old_collect_spec_sequence_bound_identities(right, variables, integer_seen);
        }
    }
}

fn old_collect_spec_memory_bound_identities(
    _memory: &SpecMemory,
    _variables: &mut BTreeSet<Variable>,
    _integer_seen: &mut SeenTerms,
) {
    // A SpecMemory is a captured execution snapshot, not lexical input to
    // the expression.  Its blocks, cells, and union overlays are therefore
    // opaque to freshness collection; callers recurse through explicit
    // pointer and expression payloads adjacent to the snapshot instead.
}

fn old_collect_spec_resource_bound_identities(
    resource: &SpecResource,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    match resource {
        SpecResource::Memory {
            base, start, end, ..
        } => {
            old_collect_spec_integer_bound_expression(base, variables, integer_seen);
            old_collect_spec_integer_bound_expression(start, variables, integer_seen);
            old_collect_spec_integer_bound_expression(end, variables, integer_seen);
        }
        SpecResource::Composite { arguments, .. } | SpecResource::Token { arguments, .. } => {
            for argument in arguments {
                old_collect_spec_integer_bound_expression(argument, variables, integer_seen);
            }
        }
    }
}

fn old_collect_spec_proposition_bound_identities(
    proposition: &SpecProposition,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    match proposition {
        SpecProposition::IntegerComparison { left, right, .. } => {
            old_collect_spec_integer_bound_variables_inner(left, variables, integer_seen);
            old_collect_spec_integer_bound_variables_inner(right, variables, integer_seen);
        }
        SpecProposition::AlgebraicComparison { left, right, .. } => {
            old_collect_spec_algebraic_bound_identities(left, variables, integer_seen);
            old_collect_spec_algebraic_bound_identities(right, variables, integer_seen);
        }
        SpecProposition::SequenceMembership { element, sequence } => {
            old_collect_spec_integer_bound_expression(element, variables, integer_seen);
            old_collect_spec_sequence_bound_identities(sequence, variables, integer_seen);
        }
        SpecProposition::SequenceComparison { left, right, .. } => {
            old_collect_spec_sequence_bound_identities(left, variables, integer_seen);
            old_collect_spec_sequence_bound_identities(right, variables, integer_seen);
        }
        SpecProposition::Comparison { left, right, .. } => {
            old_collect_spec_integer_bound_expression(left, variables, integer_seen);
            old_collect_spec_integer_bound_expression(right, variables, integer_seen);
        }
        SpecProposition::FloatClassification { expression, .. }
        | SpecProposition::Defined(expression) => {
            old_collect_spec_integer_bound_expression(expression, variables, integer_seen);
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            old_collect_spec_proposition_bound_identities(left, variables, integer_seen);
            old_collect_spec_proposition_bound_identities(right, variables, integer_seen);
        }
        SpecProposition::Not(body) => {
            old_collect_spec_proposition_bound_identities(body, variables, integer_seen);
        }
        SpecProposition::ForAllMachineInteger { variable, body, .. }
        | SpecProposition::ForAllInt32 { variable, body, .. }
        | SpecProposition::ForAllInteger { variable, body, .. }
        | SpecProposition::ForAllAlgebraic { variable, body, .. }
        | SpecProposition::ForAllPointer { variable, body, .. }
        | SpecProposition::ExistsMachineInteger { variable, body, .. }
        | SpecProposition::ExistsInt32 { variable, body, .. }
        | SpecProposition::ExistsInteger { variable, body, .. }
        | SpecProposition::ExistsAlgebraic { variable, body, .. }
        | SpecProposition::ExistsPointer { variable, body, .. } => {
            variables.insert(*variable);
            old_collect_spec_proposition_bound_identities(body, variables, integer_seen);
        }
        SpecProposition::Predicate { arguments, .. } => {
            for argument in arguments {
                match argument {
                    SpecPredicateArgument::Value(value) => {
                        old_collect_spec_integer_bound_expression(value, variables, integer_seen);
                    }
                    SpecPredicateArgument::ArrayRef { memory, pointer } => {
                        old_collect_spec_memory_bound_identities(memory, variables, integer_seen);
                        old_collect_spec_integer_bound_expression(pointer, variables, integer_seen);
                    }
                }
            }
        }
        SpecProposition::ResourceSeparate { left, right }
        | SpecProposition::ResourceContains {
            parent: left,
            child: right,
        } => {
            old_collect_spec_resource_bound_identities(left, variables, integer_seen);
            old_collect_spec_resource_bound_identities(right, variables, integer_seen);
        }
        SpecProposition::MemoryInitialized { memory, base, .. } => {
            old_collect_spec_memory_bound_identities(memory, variables, integer_seen);
            old_collect_spec_integer_bound_expression(base, variables, integer_seen);
        }
        SpecProposition::ValidPlace {
            memory,
            pointer: base,
            range,
            ..
        } => {
            old_collect_spec_memory_bound_identities(memory, variables, integer_seen);
            old_collect_spec_integer_bound_expression(base, variables, integer_seen);
            if let Some((start, end)) = range {
                old_collect_spec_integer_bound_expression(start, variables, integer_seen);
                old_collect_spec_integer_bound_expression(end, variables, integer_seen);
            }
        }
        SpecProposition::MemoryLoadable {
            memory,
            base,
            start,
            end,
            ..
        } => {
            old_collect_spec_memory_bound_identities(memory, variables, integer_seen);
            old_collect_spec_integer_bound_expression(base, variables, integer_seen);
            old_collect_spec_integer_bound_expression(start, variables, integer_seen);
            old_collect_spec_integer_bound_expression(end, variables, integer_seen);
        }
    }
}

fn old_collect_spec_algebraic_expression_bitvector_variables(
    expression: &SpecAlgebraicExpression,
    variables: &mut BTreeSet<Variable>,
) {
    match &expression.node {
        SpecAlgebraicExpressionNode::ResourceField(_) => {}
        SpecAlgebraicExpressionNode::Variable(_) | SpecAlgebraicExpressionNode::Binding(_) => {}
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            for field in fields {
                match field {
                    SpecAlgebraicValue::C(field) => {
                        old_collect_spec_expression_bitvector_variables(field, variables)
                    }
                    SpecAlgebraicValue::Integer(value) => {
                        old_collect_spec_integer_variables(value, variables)
                    }
                    SpecAlgebraicValue::Algebraic(field) => {
                        old_collect_spec_algebraic_expression_bitvector_variables(field, variables)
                    }
                }
            }
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            old_collect_spec_algebraic_expression_bitvector_variables(scrutinee, variables);
            for arm in arms {
                old_collect_spec_algebraic_expression_bitvector_variables(&arm.body, variables);
            }
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                old_collect_spec_function_argument_bitvector_variables(argument, variables);
            }
        }
    }
}

fn old_collect_spec_function_argument_bitvector_variables(
    argument: &SpecPureFunctionArgument,
    variables: &mut BTreeSet<Variable>,
) {
    match argument {
        // Correct the historical omission alongside the production collector:
        // Integer arguments carry free identities regardless of the result type.
        SpecPureFunctionArgument::Integer(expression) => {
            old_collect_spec_integer_variables(expression, variables)
        }
        SpecPureFunctionArgument::Value(expression) => {
            old_collect_spec_expression_bitvector_variables(expression, variables)
        }
        SpecPureFunctionArgument::Algebraic(expression) => {
            old_collect_spec_algebraic_expression_bitvector_variables(expression, variables)
        }
        SpecPureFunctionArgument::ArrayRef {
            memory, pointer, ..
        } => {
            old_collect_spec_memory_bitvector_variables(memory, variables);
            old_collect_spec_expression_bitvector_variables(pointer, variables);
        }
    }
}

fn old_collect_spec_sequence_bitvector_variables(
    sequence: &SpecSequenceExpression,
    variables: &mut BTreeSet<Variable>,
) {
    match sequence {
        SpecSequenceExpression::Literal(elements) => {
            for element in elements {
                old_collect_spec_expression_bitvector_variables(element, variables);
            }
        }
        SpecSequenceExpression::Concat(left, right) => {
            old_collect_spec_sequence_bitvector_variables(left, variables);
            old_collect_spec_sequence_bitvector_variables(right, variables);
        }
    }
}

fn old_collect_spec_resource_bitvector_variables(
    resource: &SpecResource,
    variables: &mut BTreeSet<Variable>,
) {
    match resource {
        SpecResource::Memory {
            base, start, end, ..
        } => {
            old_collect_spec_expression_bitvector_variables(base, variables);
            old_collect_spec_expression_bitvector_variables(start, variables);
            old_collect_spec_expression_bitvector_variables(end, variables);
        }
        SpecResource::Composite { arguments, .. } | SpecResource::Token { arguments, .. } => {
            for argument in arguments {
                old_collect_spec_expression_bitvector_variables(argument, variables);
            }
        }
    }
}

#[test]
fn spec_collectors_agree_with_their_recursive_originals() {
    let mut generator = Gen::new(0x9e37_79b9_7f4a_7c15);
    let (mut propositions, mut integers) = (0, 0);
    for round in 0..4000 {
        let depth = 1 + (round % 5) as u32;
        let proposition = generator.prop(depth);
        let (mut old, mut new) = (BTreeSet::new(), BTreeSet::new());
        old_collect_spec_proposition_bitvector_variables(&proposition, &mut old);
        collect_spec_proposition_bitvector_variables(&proposition, &mut new);
        assert_eq!(new, old, "{proposition:?}");
        propositions += usize::from(!old.is_empty());
        let (mut old, mut new) = (BTreeSet::new(), BTreeSet::new());
        old_collect_spec_proposition_bound_identities(
            &proposition,
            &mut old,
            &mut SeenTerms::default(),
        );
        collect_spec_bound_identities(
            SpecNode::Proposition(&proposition),
            &mut new,
            &mut SeenTerms::default(),
        );
        assert_eq!(new, old, "{proposition:?}");

        let integer = generator.int(depth);
        let (mut old, mut new) = (BTreeSet::new(), BTreeSet::new());
        old_collect_spec_integer_variables(&integer, &mut old);
        collect_spec_integer_variables(&integer, &mut new);
        assert_eq!(new, old, "{integer:?}");
        integers += usize::from(!old.is_empty());
        let (mut old, mut new) = (BTreeSet::new(), BTreeSet::new());
        old_collect_spec_integer_bound_variables(&integer, &mut old);
        collect_spec_integer_bound_variables(&integer, &mut new);
        assert_eq!(new, old, "{integer:?}");

        let algebraic = generator.alg(depth);
        let (mut old, mut new) = (BTreeSet::new(), BTreeSet::new());
        old_collect_spec_algebraic_expression_bitvector_variables(&algebraic, &mut old);
        collect_spec_algebraic_expression_bitvector_variables(&algebraic, &mut new);
        assert_eq!(new, old, "{algebraic:?}");
    }
    // Both empty and non-empty answers occur often enough to mean something.
    for count in [propositions, integers] {
        assert!((200..3800).contains(&count), "{propositions} {integers}");
    }
}
