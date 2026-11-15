use super::*;

#[test]
fn sequence_child_spelling_visits_only_the_written_elements() {
    let mut samples = Vec::new();
    for length in [32, 128, 512] {
        let singleton = |index| {
            ContractExpression::SequenceLiteral(vec![ContractExpression::ProgramExpression(
                ProgramExpression::Variable(format!("v{index}")),
            )])
        };
        // Deliberately skewed source concatenation must not make flattening
        // revisit prefixes or recurse on the Rust stack.
        let sequence = (1..length).fold(singleton(0), |left, index| {
            ContractExpression::SequenceConcat(Box::new(left), Box::new(singleton(index)))
        });
        let goal = ClickProposition::Comparison {
            left: sequence.clone(),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::Old(Box::new(sequence)),
        };
        let (children, work) = crate::instrumentation::measure_deterministic_work(|| {
            surface_logical_children(&goal, true).unwrap()
        });
        let mut pending = vec![children.0, children.1];
        let mut leaves = 0;
        while let Some(child) = pending.pop() {
            match child {
                ClickProposition::And(left, right) => pending.extend([*right, *left]),
                ClickProposition::Comparison {
                    right: ContractExpression::Old(_),
                    ..
                } => leaves += 1,
                other => panic!("lost an element's state: {other:?}"),
            }
        }
        assert_eq!(leaves, length);
        assert!(work <= length * 12, "{length} elements took {work} work");
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}

#[test]
fn computed_transport_read_selection_is_linear_in_written_expression() {
    for length in [32, 128, 512] {
        let read = ContractExpression::ProgramExpression(ProgramExpression::Load(Box::new(
            ProgramExpression::Variable("p".into()),
        )));
        let expression = (1..length).fold(read.clone(), |left, _| {
            ContractExpression::Add(Box::new(left), Box::new(read.clone()))
        });
        let historical = ContractExpression::At {
            selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Region(0),
                kind: ProgramPointKind::Entry,
            }),
            expression: Box::new(expression.clone()),
        };
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            scalar_preservation_read_leaves(vec![(historical, expression)]).unwrap()
        });
        assert_eq!(
            selected.len(),
            1,
            "one equality preserves every repeated read"
        );
        assert!(work <= length * 3, "{length} leaves took {work} work");
    }
}
