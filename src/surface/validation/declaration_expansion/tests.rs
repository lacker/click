use super::*;

fn check_isolated_program(value: i32, expected: i32) {
    let c_source = format!("int32 answer(void) {{ return {value}; }}");
    let click_source = format!(
        r#"
        verifying "answer.c";
        predicate wanted(x: int32) {{ x == {expected} }}
        int32 answer() {{
            ensures wanted(result) by {{ execute(); unfold(wanted); simp(); }}
        }}
        "#
    );
    let result = verify_c0_sources(&click_source, &[("answer.c", &c_source)]);
    if value == expected {
        result.expect("each program must use its own wanted predicate");
    } else {
        assert!(
            result.is_err(),
            "a preceding successful proof must not leak"
        );
    }
}

#[test]
fn standard_library_initialization_is_constant_across_verification_sizes() {
    // Count initialization, not elapsed time: repeated fixture threads must
    // not parse the prelude again as the number of verifications increases.
    for count in [1, 2, 4, 8] {
        std::thread::scope(|scope| {
            let handles = (0..count)
                .map(|value| {
                    scope.spawn(move || {
                        check_isolated_program(value, value);
                        check_isolated_program(value, value + 1);
                        check_isolated_program(value + 1, value + 1);
                    })
                })
                .collect::<Vec<_>>();
            for handle in handles {
                handle.join().unwrap();
            }
        });
        assert_eq!(
            STANDARD_LIBRARY_PARSES.load(std::sync::atomic::Ordering::Relaxed),
            1,
            "prelude initialization must remain constant at {count} fixture threads"
        );
    }
}

#[test]
fn standard_library_cache_preserves_all_declarations() {
    let fresh =
        expand_declared_resource_clauses(parser::parse_file_items(CLICK_STANDARD_LIBRARY).unwrap())
            .unwrap();
    assert_eq!(standard_library().unwrap(), &fresh);
    // Accessors return independently owned categories, never a mutable view
    // of the process-wide syntax or a clone of unrelated categories.
    let empty = parser::parse_file_items("").unwrap();
    let mut functions = combined_external_function_blocks(&empty).unwrap();
    assert!(!functions.is_empty());
    functions.clear();
    assert_eq!(
        combined_external_function_blocks(&empty).unwrap(),
        fresh.function_blocks()
    );
    assert_eq!(
        combined_algebraic_type_definitions(&empty).unwrap(),
        parser::parse_file_items(CLICK_STANDARD_LIBRARY)
            .unwrap()
            .algebraic_type_definitions
    );
}
