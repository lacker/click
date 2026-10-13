use super::*;

/// Check the resource-model dependency claim on a registered definition.
/// Opaque pure calls depend on their explicit arguments; memory is captured by
/// predicate memory arguments. This walk borrows the definition and is linear
/// in its written body, without consulting unrelated definitions or proof facts.
pub(in crate::kernel) fn observes_resource_state(proposition: &SpecProposition) -> bool {
    use super::walk::{SpecNode, Visit, WalkBudget, Walked, walk_spec};
    let walked = walk_spec(
        SpecNode::Proposition(proposition),
        WalkBudget::Deadline,
        |node| match node {
            SpecNode::Proposition(
                SpecProposition::Predicate {
                    resource_state_dependent: true,
                    ..
                }
                | SpecProposition::ResourceSeparate { .. }
                | SpecProposition::ResourceContains { .. },
            )
            | SpecNode::Expression(
                SpecExpression::CountedResourceCount { .. } | SpecExpression::ResourceField { .. },
            )
            | SpecNode::Integer(SpecIntegerExpression::ResourceField(_)) => Visit::Stop(()),
            SpecNode::Algebraic(algebraic)
                if matches!(
                    algebraic.node,
                    SpecAlgebraicExpressionNode::ResourceField(_)
                ) =>
            {
                Visit::Stop(())
            }
            _ => Visit::Descend,
        },
    );
    // An incomplete walk cannot certify independence from the model.
    !matches!(walked, Walked::Completed)
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
