use super::*;

#[test]
fn pure_callback_preparation_does_not_enumerate_the_resource_frame() {
    let contract = interface(0);
    for count in [0, 16, 64, 256] {
        let resources = ResourceContext::new().unchecked_with_facts(
            (0..count).map(|index| CResourceFact::own_token(format!("token{index}"), vec![])),
        );
        assert!(resources.storage.materialized.get().is_none());
        let state = CState::new().with_resource_context(resources.clone());
        let transfer = prepare_function_resource_transfer(
            &state,
            &CState::new(),
            contract.template(),
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
            false,
        )
        .unwrap()
        .unwrap();
        assert!(transfer.callee_resources.is_empty());
        assert!(std::sync::Arc::ptr_eq(
            &resources.storage,
            &transfer.caller_resources_after_requirements.storage
        ));
        assert!(
            resources.storage.materialized.get().is_none(),
            "preparation must not enumerate {count} unrelated resources"
        );
    }
}

fn interface(index: usize) -> CFunctionContract {
    let function = c_function(
        CType::Int32,
        format!("Bound{index}"),
        vec![c_parameter("value", CType::Int32)],
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        vec![],
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::GreaterEqual,
            right: SpecExpression::Value(int32((-(index as i32)) as u32)),
        }],
        vec![],
        vec![],
        true,
    );
    CFunctionContract::new(format!("Bound{index}"), function).unwrap()
}

#[test]
fn callback_conjunction_shares_call_budget_and_scales_with_interfaces() {
    let mut samples = Vec::new();
    for count in [1, 8, 32, 128] {
        let contracts = (0..count).map(interface).collect::<Vec<_>>();
        let contracts = contracts.iter().collect::<Vec<_>>();
        let mut budget = ExecutionBudget::default()
            .with_function_calls(1)
            .with_paths(1);
        let initial_expressions = budget.expression_steps;
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_c_function_contracts_paths(
                &CState::new(),
                &contracts,
                &[c_int32_literal(7)],
                &PureFactContext::new(),
                &CExecutionEnvironment::new(),
                &mut budget,
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        assert!(matches!(paths[0].outcome, CFunctionOutcome::Return { .. }));
        assert!(paths[0].obligations.is_empty());
        assert!(paths[0].facts.len() >= count);
        assert_eq!(budget.function_calls, 0);
        assert_eq!(budget.next_kernel_variable(), 2);
        samples.push((count, work, initial_expressions - budget.expression_steps));
    }
    for pair in samples.windows(2) {
        let ratio = pair[1].0 / pair[0].0;
        assert!(
            pair[1].1 <= (pair[0].1 + 16) * ratio,
            "conjunction work must scale with relevant interfaces: {samples:?}"
        );
        assert!(
            pair[1].2 <= (pair[0].2 + 4) * ratio,
            "conjunction expression work must scale linearly: {samples:?}"
        );
    }
}

#[test]
fn callback_conjunction_does_not_visit_unrelated_functions() {
    let contracts = vec![interface(0), interface(1)];
    let contracts = contracts.iter().collect::<Vec<_>>();
    let mut samples = Vec::new();
    for count in [0, 16, 64, 256] {
        let mut environment = CExecutionEnvironment::new();
        for index in 0..count {
            environment = environment.with_function(c_function(
                CType::Int32,
                format!("unrelated{index}"),
                vec![],
                c_return(c_int32_literal(0)),
            ));
        }
        let mut budget = ExecutionBudget::default()
            .with_function_calls(1)
            .with_paths(1);
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_c_function_contracts_paths(
                &CState::new(),
                &contracts,
                &[c_int32_literal(7)],
                &PureFactContext::new(),
                &environment,
                &mut budget,
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        samples.push((work, budget));
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "unrelated functions must not change call work: {samples:?}"
    );
}
