use super::*;

#[test]
fn resource_call_arguments_are_checked_in_kernel_and_fields_are_fresh() {
    let schema = ResourceFieldSchema::new(vec![(
        "revision".into(),
        ResourceFieldType::C(CType::Int32),
    )])
    .unwrap();
    let parameter = |identity| CResourceSpec::Instance {
        identity: Variable(identity),
        binder: format!("cell{identity}"),
        schema: schema.clone(),
        resource: Box::new(CResourceSpec::Composite {
            access: CResourceAccessMode::Own,
            name: "marker".into(),
            arguments: vec![],
            parameter_types: vec![],
        }),
    };
    let function = c_function(CType::Void, "touch", vec![], CStatement::Skip)
        .with_contract(vec![], vec![], vec![], vec![], true)
        .with_resource_summary(vec![parameter(0)], vec![parameter(0)]);
    let contract = CFunctionContract::new("Touch", function)
        .unwrap()
        .with_proof_parameters(vec![parameter(0)]);
    // Reserve the identifier immediately after the call's memory/result IDs.
    // Post-field generation must skip it, not accidentally preserve the field.
    let before = ResourceInstance::new(
        Variable(10),
        "marker".into(),
        vec![].into(),
        schema.clone(),
        vec![AlgebraicValue::C(symbolic_call_result(
            CType::Int32,
            Variable(1_000_002),
        ))]
        .into(),
    )
    .unwrap();
    let state = CState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(before.clone()))),
    );
    let environment = CExecutionEnvironment::new()
        .with_selected_call_contract("Touch")
        .with_selected_call_resource_arguments(vec![Variable(10)]);
    let run =
        |state: &CState, contract: &CFunctionContract, environment: &CExecutionEnvironment| {
            execute_c_function_contracts_paths(
                state,
                &[contract],
                &[],
                &PureFactContext::new(),
                environment,
                &mut ExecutionBudget::default(),
            )
            .unwrap()
        };
    let paths = run(&state, &contract, &environment);
    let CFunctionOutcome::Return { state: after, .. } = &paths[0].outcome else {
        panic!("call failed: {:?}", paths[0].outcome);
    };
    assert!(after.resource_bindings.is_none());
    let returned = after.owned_resource_instance(Variable(10)).unwrap();
    assert_ne!(returned.fields(), before.fields());
    for (state, contract, environment) in [
        (CState::new(), contract.clone(), environment.clone()),
        (
            state.clone(),
            contract.clone(),
            environment
                .clone()
                .with_selected_call_resource_arguments(vec![]),
        ),
        (
            state.clone(),
            contract
                .clone()
                .with_proof_parameters(vec![parameter(0), parameter(1)]),
            environment
                .clone()
                .with_selected_call_resource_arguments(vec![Variable(10), Variable(10)]),
        ),
        (
            state.clone(),
            contract.clone(),
            environment
                .clone()
                .with_selected_call_resource_arguments(vec![Variable(99)]),
        ),
    ] {
        assert!(matches!(
            run(&state, &contract, &environment)[0].outcome,
            CFunctionOutcome::RuntimeError(_)
        ));
    }
}

#[test]
fn executed_refinement_checks_the_exact_call_and_source_premises() {
    check_executed_refinement_shape(CType::Void, false);
}

#[test]
fn executed_refinement_requires_forwarding_the_exact_typed_call_result() {
    for return_type in [CType::Int32, CType::Int64, CType::Int32Pointer] {
        check_executed_refinement_shape(return_type, false);
        check_executed_refinement_shape(return_type, true);
    }
}

fn check_executed_refinement_shape(return_type: CType, alter_result: bool) {
    let template = c_function(
        return_type,
        "interface",
        vec![c_parameter("x", CType::Int32)],
        CStatement::Skip,
    )
    .with_contract(vec![], vec![], vec![], vec![], true);
    let source = CFunctionContract::new("Source", template.clone()).unwrap();
    let target = CFunctionContract::new("Target", template.clone()).unwrap();
    let pointer_type = source.function_pointer_type();
    let premise = SpecProposition::Predicate {
        name: source.predicate_name(),
        arguments: vec![SpecPredicateArgument::Value(SpecExpression::CExpression(
            c_variable("callback"),
        ))],
    };
    let conclusion = Proposition::Predicate {
        name: target.predicate_name(),
        arguments: vec![
            Term::CState(CState::new()),
            Term::CValue(CValue::Pointer(CPointerValue::new(
                Pointer {
                    block: PointerBlock::FunctionSymbolic(Variable(0)),
                    offset: PointerOffsetTerm::Constant(0),
                },
                pointer_type,
            ))),
        ],
    };
    let environment = CExecutionEnvironment::new()
        .with_function_contract(source)
        .with_function_contract(target);
    // Isolate the implication boundary: its input is an already trusted rule.
    // Ordinary execution certification is covered by the mdtests.
    for (callee, argument, sources, extra_premise, valid) in [
        ("callback", c_variable("x"), vec!["Source"], false, true),
        ("other", c_variable("x"), vec!["Source"], false, false),
        ("callback", c_int32_literal(1), vec!["Source"], false, false),
        ("callback", c_variable("x"), vec!["Target"], false, false),
        ("callback", c_variable("x"), vec![], false, false),
        ("callback", c_variable("x"), vec!["Source"], true, false),
    ] {
        let mut requirements = vec![premise.clone()];
        if extra_premise {
            requirements.insert(0, premise.clone());
        }
        let function = c_function(
            return_type,
            "wrapper",
            vec![
                c_parameter("x", CType::Int32),
                c_parameter("callback", pointer_type),
            ],
            if return_type == CType::Void {
                CStatement::Call {
                    function_name: callee.to_string(),
                    arguments: vec![argument],
                }
            } else {
                c_seq(
                    c_call_assign("result", callee, vec![argument]),
                    c_return(if alter_result {
                        c_int32_literal(0)
                    } else {
                        c_variable("result")
                    }),
                )
            },
        )
        .with_contract(requirements, vec![], vec![], vec![], true);
        assert_eq!(
            crate::kernel::prove_executed_contract_refinement(
                &environment,
                &sources,
                "Target",
                conclusion.clone(),
                &CVerifiedFunctionRule { function },
            )
            .is_some(),
            valid && !alter_result
        );
    }
}

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
    check_callback_interface_scaling(false);
}

#[test]
fn selected_callback_shares_call_budget_and_scales_with_interfaces() {
    check_callback_interface_scaling(true);
}

fn check_callback_interface_scaling(select: bool) {
    let mut samples = Vec::new();
    for count in [1, 8, 32, 128] {
        let contracts = (0..count).map(interface).collect::<Vec<_>>();
        let contracts = contracts.iter().collect::<Vec<_>>();
        let mut budget = ExecutionBudget::default()
            .with_function_calls(1)
            .with_paths(1);
        let initial_expressions = budget.expression_steps;
        let environment = if select {
            CExecutionEnvironment::new().with_selected_call_contract(&format!("Bound{}", count - 1))
        } else {
            CExecutionEnvironment::new()
        };
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
    check_unrelated_functions(false);
}

#[test]
fn selected_callback_does_not_visit_unrelated_functions() {
    check_unrelated_functions(true);
}

fn check_unrelated_functions(select: bool) {
    let contracts = [interface(0), interface(1)];
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
        if select {
            let selected = environment.clone().with_selected_call_contract("Bound1");
            assert!(selected.shares_all_storage_with(&environment));
            assert_ne!(selected, environment);
            assert!(environment.selected_call_contract.is_none());
            environment = selected;
        }
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

/// Contract refinement decides one named clause by the exact routes only:
/// indexed exact membership and the frozen condition checker on a bare
/// condition. Neither a decided clause nor a rejected one may scan the
/// ambient facts, so growing the unrelated context must not change the work.
#[test]
fn contract_refinement_work_is_flat_in_unrelated_facts() {
    let variable = |index| Bitvector32Term::Variable(Variable(index));
    let bound = ConditionTerm::signed_less_than(variable(70_001), Bitvector32Term::Constant(10));
    let equality = ConditionTerm::equal(variable(70_002), variable(70_003));
    let refuted = ConditionTerm::signed_less_than(variable(70_005), Bitvector32Term::Constant(0));
    let unproved = Proposition::Predicate {
        name: "unproved_refinement_clause".to_string(),
        arguments: vec![],
    };
    // An exactly available bare condition.
    let exact = Proposition::ConditionIs(equality.clone(), true);
    // A bare condition the frozen checker decides against, read through `not`.
    let negated = Proposition::Not(Box::new(Proposition::ConditionIs(refuted.clone(), true)));
    // Compound clauses no exact route establishes. The logical descent that
    // used to split these now belongs to the refinement theorem's proof, so
    // the kernel answers no — and must do so without an ambient scan.
    let structural = Proposition::And(
        Box::new(Proposition::ConditionIs(bound.clone(), true)),
        Box::new(Proposition::Or(
            Box::new(Proposition::ConditionIs(equality.clone(), true)),
            Box::new(unproved.clone()),
        )),
    );
    let guarded = Proposition::Implies(
        Box::new(Proposition::ConditionIs(refuted.clone(), true)),
        Box::new(unproved),
    );

    let samples = [16, 64, 256, 1024]
        .into_iter()
        .map(|size| {
            let mut assumptions = PureFactContext::new()
                .assume_condition(bound.clone(), true)
                .assume_condition(equality.clone(), true)
                .assume_condition(refuted.clone(), false);
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(Variable(71_000 + index as u64)),
                        Bitvector32Term::Constant(index as u32 + 1),
                    ),
                    true,
                );
            }
            let measure = |goal: &Proposition, expected: bool| {
                let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
                    contract_refinement_proves(&assumptions, goal)
                });
                assert_eq!(
                    proved, expected,
                    "refinement answer changed with {size} unrelated facts"
                );
                work
            };
            (
                size,
                measure(&exact, true),
                measure(&negated, true),
                measure(&structural, false),
                measure(&guarded, false),
            )
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| {
            pair[0].1 == pair[1].1
                && pair[0].2 == pair[1].2
                && pair[0].3 == pair[1].3
                && pair[0].4 == pair[1].4
        }),
        "refinement checking must not scan unrelated ambient facts: {samples:?}"
    );
}
