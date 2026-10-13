use super::*;

/// Check the resource-model dependency claim on a registered definition.
/// Opaque pure calls depend on their explicit arguments; memory is captured by
/// predicate memory arguments. This walk borrows the definition and is linear
/// in its written body, without consulting unrelated definitions or proof facts.
pub(in crate::kernel) fn observes_resource_state(proposition: &SpecProposition) -> bool {
    enum Node<'a> {
        Proposition(&'a SpecProposition),
        Expression(&'a SpecExpression),
        Integer(&'a SpecIntegerExpression),
        Algebraic(&'a SpecAlgebraicExpression),
        Sequence(&'a SpecSequenceExpression),
        Argument(&'a SpecPureFunctionArgument),
    }
    let mut pending = vec![Node::Proposition(proposition)];
    while let Some(node) = pending.pop() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            // An incomplete walk cannot certify independence from the model.
            return true;
        }
        match node {
            Node::Proposition(proposition) => match proposition {
                SpecProposition::Comparison { left, right, .. } => {
                    pending.extend([Node::Expression(left), Node::Expression(right)]);
                }
                SpecProposition::IntegerComparison { left, right, .. } => {
                    pending.extend([Node::Integer(left), Node::Integer(right)]);
                }
                SpecProposition::AlgebraicComparison { left, right, .. } => {
                    pending.extend([Node::Algebraic(left), Node::Algebraic(right)]);
                }
                SpecProposition::SequenceComparison { left, right, .. } => {
                    pending.extend([Node::Sequence(left), Node::Sequence(right)]);
                }
                SpecProposition::SequenceMembership { element, sequence } => {
                    pending.extend([Node::Expression(element), Node::Sequence(sequence)]);
                }
                SpecProposition::ValidPlace {
                    pointer: expression,
                    ..
                }
                | SpecProposition::Defined(expression)
                | SpecProposition::FloatClassification { expression, .. } => {
                    pending.push(Node::Expression(expression));
                }
                SpecProposition::And(left, right)
                | SpecProposition::Or(left, right)
                | SpecProposition::Implies(left, right) => {
                    pending.extend([Node::Proposition(left), Node::Proposition(right)]);
                }
                SpecProposition::Not(body)
                | SpecProposition::ForAllMachineInteger { body, .. }
                | SpecProposition::ForAllInt32 { body, .. }
                | SpecProposition::ForAllInteger { body, .. }
                | SpecProposition::ForAllAlgebraic { body, .. }
                | SpecProposition::ForAllPointer { body, .. }
                | SpecProposition::ExistsMachineInteger { body, .. }
                | SpecProposition::ExistsInt32 { body, .. }
                | SpecProposition::ExistsInteger { body, .. }
                | SpecProposition::ExistsAlgebraic { body, .. }
                | SpecProposition::ExistsPointer { body, .. } => {
                    pending.push(Node::Proposition(body));
                }
                SpecProposition::Predicate {
                    resource_state_dependent,
                    arguments,
                    ..
                } => {
                    if *resource_state_dependent {
                        return true;
                    }
                    for argument in arguments {
                        pending.push(Node::Expression(match argument {
                            SpecPredicateArgument::Value(expression)
                            | SpecPredicateArgument::ArrayRef {
                                pointer: expression,
                                ..
                            } => expression,
                        }));
                    }
                }
                SpecProposition::MemoryInitialized { base, .. } => {
                    pending.push(Node::Expression(base))
                }
                SpecProposition::MemoryLoadable {
                    base, start, end, ..
                } => {
                    pending.extend([
                        Node::Expression(base),
                        Node::Expression(start),
                        Node::Expression(end),
                    ]);
                }
                SpecProposition::ResourceSeparate { .. }
                | SpecProposition::ResourceContains { .. } => return true,
            },
            Node::Expression(expression) => match expression {
                SpecExpression::CountedResourceCount { .. }
                | SpecExpression::ResourceField { .. } => return true,
                SpecExpression::PureFunctionApplication { arguments, .. } => {
                    pending.extend(arguments.iter().map(Node::Argument));
                }
                SpecExpression::Value(_) | SpecExpression::CExpression(_) => {}
                SpecExpression::IntegerToMachine { value, .. } => {
                    pending.push(Node::Integer(value))
                }
                crate::kernel::binary_spec_expression!(left, right) => {
                    pending.extend([Node::Expression(left), Node::Expression(right)]);
                }
                SpecExpression::BitwiseNot(inner)
                | SpecExpression::Cast(inner, _)
                | SpecExpression::LoopEntrySnapshot(inner) => pending.push(Node::Expression(inner)),
                SpecExpression::MemoryLoad { pointer, .. }
                | SpecExpression::AggregateFieldValue { pointer, .. } => {
                    pending.push(Node::Expression(pointer))
                }
                SpecExpression::PointerOffset {
                    pointer, elements, ..
                } => {
                    pending.extend([Node::Expression(pointer), Node::Expression(elements)]);
                }
                SpecExpression::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    pending.extend([
                        Node::Proposition(condition),
                        Node::Expression(then_branch),
                        Node::Expression(else_branch),
                    ]);
                }
                SpecExpression::Let { value, body, .. } => {
                    pending.extend([Node::Expression(value), Node::Expression(body)]);
                }
                SpecExpression::RangeFold {
                    start,
                    end,
                    initial,
                    body,
                    ..
                } => {
                    pending.extend([
                        Node::Expression(start),
                        Node::Expression(end),
                        Node::Expression(initial),
                        Node::Expression(body),
                    ]);
                }
                SpecExpression::AlgebraicMatch { scrutinee, arms } => {
                    pending.push(Node::Algebraic(scrutinee));
                    pending.extend(arms.iter().map(|arm| Node::Expression(&arm.body)));
                }
            },
            Node::Integer(integer) => match integer {
                SpecIntegerExpression::ResourceField(_) => return true,
                SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
                    pending.extend(arguments.iter().map(Node::Argument));
                }
                SpecIntegerExpression::Term(_) => {}
                SpecIntegerExpression::FromMachine(expression) => {
                    pending.push(Node::Expression(expression))
                }
                SpecIntegerExpression::Negate(inner) => pending.push(Node::Integer(inner)),
                crate::kernel::binary_spec_integer_expression!(left, right) => {
                    pending.extend([Node::Integer(left), Node::Integer(right)]);
                }
                SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
                    pending.push(Node::Algebraic(scrutinee));
                    pending.extend(arms.iter().map(|arm| Node::Integer(&arm.body)));
                }
                SpecIntegerExpression::RangeFold {
                    index,
                    initial,
                    body,
                    ..
                } => {
                    pending.extend([Node::Integer(initial), Node::Integer(body)]);
                    match index {
                        SpecIntegerRangeFoldIndex::Int32 { start, end }
                        | SpecIntegerRangeFoldIndex::UInt64 { start, end } => {
                            pending.extend([Node::Expression(start), Node::Expression(end)]);
                        }
                        SpecIntegerRangeFoldIndex::Integer { start, end } => {
                            pending.extend([Node::Integer(start), Node::Integer(end)]);
                        }
                    }
                }
            },
            Node::Argument(argument) => pending.push(match argument {
                SpecPureFunctionArgument::Value(expression)
                | SpecPureFunctionArgument::ArrayRef {
                    pointer: expression,
                    ..
                } => Node::Expression(expression),
                SpecPureFunctionArgument::Integer(integer) => Node::Integer(integer),
                SpecPureFunctionArgument::Algebraic(algebraic) => Node::Algebraic(algebraic),
            }),
            Node::Sequence(sequence) => match sequence {
                SpecSequenceExpression::Literal(elements) => {
                    pending.extend(elements.iter().map(Node::Expression));
                }
                SpecSequenceExpression::Concat(left, right) => {
                    pending.extend([Node::Sequence(left), Node::Sequence(right)]);
                }
            },
            Node::Algebraic(algebraic) => match &algebraic.node {
                SpecAlgebraicExpressionNode::Variable(_)
                | SpecAlgebraicExpressionNode::Binding(_) => {}
                SpecAlgebraicExpressionNode::ResourceField(_) => return true,
                SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => {
                    pending.extend(arguments.iter().map(Node::Argument));
                }
                SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
                    for field in fields {
                        pending.push(match field {
                            SpecAlgebraicValue::C(expression) => Node::Expression(expression),
                            SpecAlgebraicValue::Integer(integer) => Node::Integer(integer),
                            SpecAlgebraicValue::Algebraic(algebraic) => Node::Algebraic(algebraic),
                        });
                    }
                }
                SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
                    pending.push(Node::Algebraic(scrutinee));
                    pending.extend(arms.iter().map(|arm| Node::Algebraic(&arm.body)));
                }
            },
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    fn literal() -> SpecExpression {
        SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(0)))
    }

    fn count() -> SpecExpression {
        SpecExpression::CountedResourceCount {
            name: "member".into(),
            arguments: vec![],
        }
    }

    fn predicate(dependent: bool) -> SpecProposition {
        SpecProposition::Predicate {
            name: "wrapper".into(),
            arguments: vec![],
            resource_state_dependent: dependent,
        }
    }

    #[test]
    fn registered_predicate_cannot_hide_count_dependency() {
        let nested = SpecProposition::ExistsInt32 {
            name: "witness".into(),
            variable: Variable(0),
            body: Box::new(SpecProposition::Not(Box::new(SpecProposition::Defined(
                count(),
            )))),
        };
        for body in [nested, predicate(true)] {
            let registered = CPredicateUnfolding::new(predicate(false), body);
            assert!(matches!(
                registered.predicate(),
                SpecProposition::Predicate {
                    resource_state_dependent: true,
                    ..
                }
            ));
        }
    }

    #[test]
    fn opaque_pure_calls_observe_only_explicit_resource_arguments() {
        for (argument, expected) in [(literal(), false), (count(), true)] {
            let body = SpecProposition::Defined(SpecExpression::PureFunctionApplication {
                name: "identity".into(),
                arguments: vec![SpecPureFunctionArgument::Value(argument)],
                result_type: CType::Int32,
            });
            assert_eq!(observes_resource_state(&body), expected);
        }
        let sequence = SpecProposition::SequenceMembership {
            element: literal(),
            sequence: SpecSequenceExpression::Literal(vec![count()]),
        };
        assert!(observes_resource_state(&sequence));
        let integer = SpecProposition::IntegerComparison {
            left: SpecIntegerExpression::FromMachine(Box::new(count())),
            operator: IntegerComparisonOperator::Equal,
            right: SpecIntegerExpression::Term(IntegerTerm::constant(0.into())),
        };
        assert!(observes_resource_state(&integer));
    }

    #[test]
    fn truncation_operands_preserve_predicate_resource_dependencies() {
        for remainder in [false, true] {
            for count_on_left in [false, true] {
                for dependent in [false, true] {
                    let observed = SpecIntegerExpression::FromMachine(Box::new(if dependent {
                        count()
                    } else {
                        literal()
                    }));
                    let constant = SpecIntegerExpression::Term(IntegerTerm::constant_i64(3));
                    let (left, right) = if count_on_left {
                        (observed, constant)
                    } else {
                        (constant, observed)
                    };
                    let expression = if remainder {
                        SpecIntegerExpression::TruncatingRemainder(Box::new(left), Box::new(right))
                    } else {
                        SpecIntegerExpression::TruncatingQuotient(Box::new(left), Box::new(right))
                    };
                    let body = SpecProposition::IntegerComparison {
                        left: expression,
                        operator: IntegerComparisonOperator::Equal,
                        right: SpecIntegerExpression::Term(IntegerTerm::constant_i64(0)),
                    };
                    let registered = CPredicateUnfolding::new(predicate(false), body);
                    assert!(
                        matches!(registered.predicate(), SpecProposition::Predicate {
                        resource_state_dependent, ..
                    } if *resource_state_dependent == dependent)
                    );
                }
            }
        }
    }

    #[test]
    fn predicate_dependency_scan_has_linear_deterministic_work() {
        let samples = [16, 64, 256].map(|size| {
            let mut body = SpecProposition::Defined(literal());
            for _ in 1..size {
                body = SpecProposition::And(
                    Box::new(SpecProposition::Defined(literal())),
                    Box::new(body),
                );
            }
            let (dependent, work) = crate::instrumentation::measure_deterministic_work(|| {
                observes_resource_state(&body)
            });
            assert!(!dependent);
            (size, work)
        });
        for (size, work) in samples {
            assert_eq!(
                work,
                3 * size - 1,
                "each proposition and expression is visited once"
            );
        }
    }
}
