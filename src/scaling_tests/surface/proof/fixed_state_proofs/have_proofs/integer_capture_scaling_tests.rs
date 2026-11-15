// Scaling tests of `src/surface/proof/fixed_state_proofs/have_proofs.rs` (module `integer_capture_scaling_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn integer_argument_state_selection_scales_with_referenced_names() {
    let expression = ContractExpression::Binding("used".into());
    for size in [16, 256, 4096] {
        let mut state = ExecutionState::new().with_local(
            "used",
            ProgramValue::UInt32(crate::kernel::MachineTerm::constant(7)),
        );
        let mut values = BTreeMap::new();
        for index in 0..size {
            let name = format!("unrelated_{index}");
            let value = ProgramValue::UInt32(crate::kernel::MachineTerm::constant(index));
            values.insert(name.clone(), value.clone());
            state = state.with_local(name, value);
        }
        let (selected, work) = crate::persistent::measure_persistent_work(|| {
            FixedStateLowering::for_expression(
                &expression,
                ContractEnvironment::new(&values, &ClickArrayRefs::new()),
                &state,
                &state,
                None,
            )
        });
        assert_eq!(selected.entry_values.len(), 1);
        assert_eq!(selected.current_values.len(), 1);
        assert_eq!(
            selected.current_values["used"],
            ProgramValue::UInt32(crate::kernel::MachineTerm::constant(7))
        );
        assert!(
            work <= 64,
            "{size} unrelated locals caused {work} persistent operations"
        );
    }
}

#[test]
fn proposition_state_selection_scales_with_referenced_names() {
    let proposition = ClickProposition::Comparison {
        left: ContractExpression::At {
            selector: ProgramPointSelector::Mark("before".into()),
            expression: Box::new(ContractExpression::Binding("used".into())),
        },
        operator: ComparisonOperator::Equal,
        right: ContractExpression::Old(Box::new(ContractExpression::Binding("used".into()))),
    };
    for size in [16, 64, 256, 1024] {
        let mut state = ExecutionState::new().with_local("used", crate::kernel::int32(7));
        let mut values = BTreeMap::new();
        for index in 0..size {
            let name = format!("unrelated_{index}");
            let value = crate::kernel::int32(index);
            values.insert(name.clone(), value.clone());
            state = state.with_local(name, value);
        }
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            FixedStateLowering::for_proposition(
                &proposition,
                ContractEnvironment::new(&values, &ClickArrayRefs::new()),
                &state,
                &state,
                None,
            )
        });
        assert_eq!(selected.entry_values.len(), 1);
        assert_eq!(selected.current_values.len(), 1);
        assert_eq!(selected.current_values["used"], crate::kernel::int32(7));
        assert!(
            work <= 8,
            "{size} unrelated locals caused {work} selection units"
        );
    }
}
