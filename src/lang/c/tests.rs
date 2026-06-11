use super::*;

#[test]
fn c_model_loads_from_source() {
    let loaded = loaded();

    assert!(loaded.computation("c-type-int32").is_some());
    assert!(loaded.computation("c-int32").is_some());
    assert!(loaded.computation("c-is-int32").is_some());
    assert!(loaded.computation("c-int32-lt-bits").is_some());
    assert!(loaded.computation("c-int32-lt").is_some());
    assert!(loaded.computation("c-int32-expr").is_some());
    assert!(loaded.computation("c-has-type").is_some());
    assert!(loaded.computation("c-eval-expr").is_some());
    assert!(loaded.computation("c-exec-stmt").is_some());
    assert!(loaded.computation("c-max-body").is_some());

    assert!(loaded.theorem("c_eval_expr_deterministic").is_some());
    assert!(loaded.theorem("c_exec_stmt_deterministic").is_some());
    assert!(loaded.theorem("c_int32_zero_has_type").is_some());
    assert!(loaded.theorem("c_int32_one_has_type").is_some());
    assert!(loaded.theorem("c_int32_zero_one_lt").is_some());
    assert!(loaded.theorem("c_int32_one_zero_not_lt").is_some());
    assert!(loaded.theorem("c_int32_expr_preserves_type").is_some());
    assert!(loaded.theorem("c_lt_literal_zero_one_eval").is_some());
    assert!(loaded.theorem("c_lt_literal_one_zero_eval").is_some());
    assert!(loaded.theorem("c_max_body_well_typed").is_some());
    assert!(loaded.theorem("c_max_zero_one_returns_one").is_some());
    assert!(loaded.theorem("c_max_one_zero_returns_one").is_some());
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
