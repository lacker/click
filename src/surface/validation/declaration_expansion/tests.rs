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

/// The standard library is proved by its own entry point, not by each
/// verification that uses it. This is the gate's proof of every library
/// theorem.
#[test]
fn standard_library_theorems_are_proved_by_their_own_entry_point() {
    let theorems = standard_library_theorem_definitions().unwrap();
    let verified = crate::surface::verify_standard_library()
        .unwrap_or_else(|error| panic!("standard library failed: {}", error.message()));
    let ensure_count = theorems
        .iter()
        .map(|theorem| theorem.ensures().len())
        .sum::<usize>();
    assert_eq!(verified.len(), ensure_count);
    for theorem in theorems {
        assert!(
            verified
                .iter()
                .any(|result| result.theorem_definition.name() == theorem.name()),
            "`{}` was not proved",
            theorem.name()
        );
    }
}

fn proved_theorems_during(verify: impl FnOnce()) -> Vec<String> {
    crate::surface::PROVED_THEOREMS.with(|proved| proved.borrow_mut().clear());
    verify();
    crate::surface::PROVED_THEOREMS.with(|proved| proved.take())
}

/// A verification applies library theorems as dependency declarations and
/// proves only its own theorems, however large the library grows.
#[test]
fn verification_does_not_reprove_the_standard_library() {
    let proved = proved_theorems_during(|| {
        let result = verify_click_theorems(
            r#"
            theorem uses_library(value: int32) {
                requires 1 <= value;
                ensures 0 <= value by {
                    apply(int32_positive_is_nonnegative(value));
                }
            }
            "#,
        );
        result.unwrap_or_else(|error| panic!("theorem failed: {}", error.message()));
        check_isolated_program(3, 3);
    });
    assert_eq!(proved, ["uses_library"]);
}

/// Certification accepts a pure theorem only with authority from a checked
/// proof, so a C proof that cites a library theorem needing that authority
/// checks exactly the cited theorem, not the rest of the library.
#[test]
fn certification_checks_only_the_cited_library_theorem() {
    let c_source = "int32 remainder(int32 value, int32 amount) { return value - amount; }";
    let click_source = r#"
        verifying "remainder.c";
        int32 remainder(int32 value, int32 amount) {
            requires defined(1 + amount) and value == 1 + amount;
            requires defined(value - amount);
            ensures result == 1;
        } by {
            have value - amount == 1 by {
                apply(int32_subtract_equal_sum_right_cancels(value, 1, amount)) using {
                    defined(1 + amount) and value == 1 + amount;
                    defined(value - amount);
                }
            }
            execute();
            simp();
        }
    "#;
    let proved = proved_theorems_during(|| {
        verify_c0_sources(click_source, &[("remainder.c", c_source)])
            .unwrap_or_else(|error| panic!("C proof failed: {}", error.message()));
    });
    assert_eq!(proved, ["int32_subtract_equal_sum_right_cancels"]);
}
