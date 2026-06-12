use super::*;

fn assert_c_computations_load(loaded: &LoadedC) {
    assert!(loaded.computation("c-type-int32").is_some());
    assert!(loaded.computation("c-int32").is_some());
    assert!(loaded.computation("c-is-int32").is_some());
    assert!(loaded.computation("c-int32-lt").is_some());
    assert!(loaded.computation("c-int32-add").is_some());
    assert!(loaded.computation("c-int32-expr").is_some());
    assert!(loaded.computation("c-add-expr").is_some());
    assert!(loaded.computation("c-expr-ub").is_some());
    assert!(loaded.computation("c-stmt-ub").is_some());
    assert!(loaded.computation("c-ptr").is_some());
    assert!(loaded.computation("c-ptr-eq").is_some());
    assert!(loaded.computation("c-memory-load").is_some());
    assert!(loaded.computation("c-memory-store").is_some());
    assert!(loaded.computation("c-has-type").is_some());
    assert!(loaded.computation("c-eval-expr").is_some());
    assert!(loaded.computation("c-exec-stmt").is_some());
    assert!(loaded.computation("c-max-body").is_some());
}

#[test]
fn c_model_computations_load_from_source() {
    let loaded = loaded_computation_source().expect("C computations should load");

    assert_c_computations_load(loaded);
}

#[test]
fn c_model_theorems_load_from_source() {
    let loaded = loaded();

    assert_c_computations_load(&loaded);

    assert!(loaded.theorem("c_eval_expr_deterministic").is_some());
    assert!(loaded.theorem("c_exec_stmt_deterministic").is_some());
    assert!(loaded.theorem("c_int32_zero_has_type").is_some());
    assert!(loaded.theorem("c_int32_one_has_type").is_some());
    assert!(loaded.theorem("c_int32_two_has_type").is_some());
    assert!(loaded.theorem("c_int32_max_has_type").is_some());
    assert!(loaded.theorem("c_test_ptr_zero_is_ptr").is_some());
    assert!(loaded.theorem("c_test_ptr_zero_eq_self").is_some());
    assert!(loaded.theorem("c_test_ptr_zero_ne_one").is_some());
    assert!(loaded.theorem("c_memory_empty_load_invalid").is_some());
    assert!(loaded.theorem("c_memory_load_after_store_same").is_some());
    assert!(
        loaded
            .theorem("c_memory_load_after_store_other_invalid")
            .is_some()
    );
    assert!(
        loaded
            .theorem("c_memory_store_replaces_same_address")
            .is_some()
    );
    assert!(
        loaded
            .theorem("c_memory_store_preserves_other_address")
            .is_some()
    );
    assert!(loaded.theorem("c_int32_zero_one_lt").is_some());
    assert!(loaded.theorem("c_int32_one_zero_not_lt").is_some());
    assert!(loaded.theorem("c_int32_one_one_add").is_some());
    assert!(loaded.theorem("c_int32_max_one_add_overflows").is_some());
    assert!(loaded.theorem("c_int32_expr_preserves_type").is_some());
    assert!(loaded.theorem("c_lt_literal_zero_one_eval").is_some());
    assert!(loaded.theorem("c_lt_literal_one_zero_eval").is_some());
    assert!(loaded.theorem("c_add_literal_one_one_has_type").is_some());
    assert!(loaded.theorem("c_add_literal_max_one_has_type").is_some());
    assert!(loaded.theorem("c_add_literal_one_one_eval").is_some());
    assert!(loaded.theorem("c_add_literal_max_one_ub").is_some());
    assert!(loaded.theorem("c_return_add_overflow_ub").is_some());
    assert!(loaded.theorem("c_max_body_well_typed").is_some());
    assert!(loaded.theorem("c_max_zero_one_returns_one").is_some());
    assert!(loaded.theorem("c_max_one_zero_returns_one").is_some());
    assert!(loaded.theorem("c_max_lt_returns_right").is_some());
    assert!(loaded.theorem("c_max_not_lt_returns_left").is_some());
}

#[test]
fn c_computation_layer_keeps_source_env_without_defining_theorems() {
    let loaded = loaded_computation_source().expect("C computations should load");

    assert_eq!(parsed_c_modules().expect("C modules should parse").len(), 1);
    assert!(
        parsed_c_source_env()
            .expect("C source env should exist")
            .computation("c-max-body")
            .is_some()
    );
    assert!(loaded.computation("c-max-body").is_some());
    let theorem = loaded
        .source_env()
        .theorem("c_max_zero_one_returns_one")
        .expect("theorem name should resolve");

    assert!(loaded.theorem("c_max_zero_one_returns_one").is_some());
    assert!(loaded.theory().theorem(theorem).is_none());
}

#[test]
fn c0_syntax_imports_max_body() {
    let mut loaded = loaded_computation_source()
        .expect("C computations should load")
        .clone();
    let function = syntax::parse_function(
        r#"
        int32 max(int32 a, int32 b) {
            if (a < b) {
                return b;
            } else {
                return a;
            }
        }
        "#,
    )
    .expect("max should parse");

    assert_eq!(function.name(), "max");
    assert_eq!(function.params()[0].name(), "a");
    assert_eq!(function.params()[1].name(), "b");

    let source = format!(
        "(def imported-c-max-body\n  {})",
        function.body_click_source()
    );
    loaded
        .load_computations_section("lang/c/import-test", &source)
        .expect("generated Click source should load");

    let imported = loaded
        .computation("imported-c-max-body")
        .expect("imported body should be named");
    let expected = loaded
        .computation("c-max-body")
        .expect("model max body should be named");

    assert_eq!(
        loaded.theory().computation(imported),
        loaded.theory().computation(expected)
    );
}

#[test]
fn c0_syntax_targets_megakernel_max_body() {
    let function = syntax::parse_function(
        r#"
        int32 max(int32 a, int32 b) {
            if (a < b) {
                return b;
            } else {
                return a;
            }
        }
        "#,
    )
    .expect("max should parse");
    let stmt = function.body_megakernel_stmt();

    assert_eq!(stmt, crate::megakernel::c_max_body());

    let a = crate::megakernel::Var(30);
    let b = crate::megakernel::Var(31);
    let a_bits = crate::megakernel::Bv32Term::Var(a);
    let b_bits = crate::megakernel::Bv32Term::Var(b);
    let condition = crate::megakernel::c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state = crate::megakernel::c_max_state(
        crate::megakernel::int32(a_bits),
        crate::megakernel::int32(b_bits),
    );
    let assumptions = crate::megakernel::Assumptions::new().assume_bool(condition.clone(), true);
    let theorem =
        crate::megakernel::prove_symbolic_c_execution(state.clone(), stmt.clone(), assumptions)
            .expect("parsed max should symbolically execute");

    assert_eq!(
        theorem.prop(),
        &crate::megakernel::Prop::Implies(
            Box::new(crate::megakernel::Prop::BoolIs(condition, true)),
            Box::new(crate::megakernel::Prop::CStmtExecutes {
                state: state.clone(),
                stmt,
                outcome: crate::megakernel::CStmtOutcome::Return {
                    value: crate::megakernel::int32(crate::megakernel::Bv32Term::Var(b)),
                    state,
                },
            }),
        )
    );
}

#[test]
fn c0_syntax_targets_megakernel_max_function_call() {
    let function = syntax::parse_function(
        r#"
        int32 max(int32 a, int32 b) {
            if (a < b) {
                return b;
            } else {
                return a;
            }
        }
        "#,
    )
    .expect("max should parse");
    let function = function.to_megakernel_function();

    assert_eq!(function, crate::megakernel::c_max_function());

    let state = crate::megakernel::CState::new();
    let args = vec![
        crate::megakernel::c_int32_literal(0),
        crate::megakernel::c_int32_literal(1),
    ];
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        args.clone(),
        Default::default(),
    )
    .expect("parsed max function call should execute");

    assert_eq!(
        theorem.prop(),
        &crate::megakernel::Prop::CFunctionExecutes {
            state: state.clone(),
            function,
            args,
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(1),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_megakernel_assignment_and_sequence() {
    let function = syntax::parse_function(
        r#"
        int32 inc(int32 x) {
            x = x + 1;
            return x;
        }
        "#,
    )
    .expect("assignment function should parse");
    let stmt = function.body_megakernel_stmt();
    let initial = crate::megakernel::CState::new().with_local("x", crate::megakernel::int32(1));
    let final_state = crate::megakernel::CState::new().with_local("x", crate::megakernel::int32(2));
    let theorem = crate::megakernel::prove_symbolic_c_execution(
        initial.clone(),
        stmt.clone(),
        Default::default(),
    )
    .expect("parsed assignment sequence should execute");

    assert_eq!(
        theorem.prop(),
        &crate::megakernel::Prop::CStmtExecutes {
            state: initial,
            stmt,
            outcome: crate::megakernel::CStmtOutcome::Return {
                value: crate::megakernel::int32(2),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_megakernel_assignment_function_call() {
    let function = syntax::parse_function(
        r#"
        int32 inc(int32 x) {
            x = x + 1;
            return x;
        }
        "#,
    )
    .expect("assignment function should parse");
    let function = function.to_megakernel_function();
    let state = crate::megakernel::CState::new().with_local("caller", crate::megakernel::int32(5));
    let args = vec![crate::megakernel::c_int32_literal(1)];
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        args.clone(),
        Default::default(),
    )
    .expect("parsed assignment function call should execute");

    assert_eq!(
        theorem.prop(),
        &crate::megakernel::Prop::CFunctionExecutes {
            state: state.clone(),
            function,
            args,
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(2),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_megakernel_store_and_load() {
    let function = syntax::parse_function(
        r#"
        int32 load_after_store(int32* p) {
            *p = 9;
            return *p;
        }
        "#,
    )
    .expect("store/load function should parse");

    assert_eq!(function.params()[0].ty(), syntax::C0Type::Int32Ptr);

    let ptr = crate::megakernel::Ptr {
        block: "block".to_string(),
        offset: crate::megakernel::Bv32Term::Const(0),
    };
    let stmt = function.body_megakernel_stmt();
    let initial = crate::megakernel::CState::new()
        .with_local("p", crate::megakernel::CValue::Ptr(ptr.clone()));
    let final_state = crate::megakernel::CState::new()
        .with_local("p", crate::megakernel::CValue::Ptr(ptr.clone()))
        .with_memory(crate::megakernel::CMemory::new().store(ptr, crate::megakernel::int32(9)));
    let theorem = crate::megakernel::prove_symbolic_c_execution(
        initial.clone(),
        stmt.clone(),
        Default::default(),
    )
    .expect("parsed store/load should execute");

    assert_eq!(
        theorem.prop(),
        &crate::megakernel::Prop::CStmtExecutes {
            state: initial,
            stmt,
            outcome: crate::megakernel::CStmtOutcome::Return {
                value: crate::megakernel::int32(9),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_megakernel_store_and_load_function_call() {
    let function = syntax::parse_function(
        r#"
        int32 load_after_store(int32* p) {
            *p = 9;
            return *p;
        }
        "#,
    )
    .expect("store/load function should parse")
    .to_megakernel_function();

    let ptr = crate::megakernel::Ptr {
        block: "block".to_string(),
        offset: crate::megakernel::Bv32Term::Const(0),
    };
    let state = crate::megakernel::CState::new().with_local("caller", crate::megakernel::int32(7));
    let args = vec![crate::megakernel::c_ptr_value(ptr.clone())];
    let final_state = crate::megakernel::CState::new()
        .with_local("caller", crate::megakernel::int32(7))
        .with_memory(crate::megakernel::CMemory::new().store(ptr, crate::megakernel::int32(9)));
    let theorem = crate::megakernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        args.clone(),
        Default::default(),
    )
    .expect("parsed store/load function call should execute");

    assert_eq!(
        theorem.prop(),
        &crate::megakernel::Prop::CFunctionExecutes {
            state,
            function,
            args,
            outcome: crate::megakernel::CFunctionOutcome::Return {
                value: crate::megakernel::int32(9),
                state: final_state,
            },
        }
    );
}
