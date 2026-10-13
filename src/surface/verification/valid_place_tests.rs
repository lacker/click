use super::*;

fn verify(body: &str, contract: &str, caller: &str) -> Result<(), String> {
    let c = format!("int helper(int* p) {{ {body} return 1; }} int caller(void) {{ {caller} }}");
    let click = format!(
        "verifying \"valid_place.c\"; int32 helper(int32* p) {{ {contract} ensures result == 1; }} by {{ execute(); simp(); }} int32 caller() {{ ensures result == 0; }} by {{ execute(); simp(); }}"
    );
    verify_c0_sources(&click, &[("valid_place.c", c.as_str())])
        .map(|_| ())
        .map_err(|e| format!("{e:?}"))
}

#[test]
fn valid_place_checks_an_uninitialized_c_object_at_a_modular_call() {
    verify(
        "",
        "requires valid_place(p);",
        "int value; helper(&value); return 0;",
    )
    .unwrap();
}

#[test]
fn valid_place_does_not_grant_read_or_write_permission() {
    for body in ["*p = 0;", "int value = *p;"] {
        assert!(
            verify(
                body,
                "requires valid_place(p);",
                "int value = 0; helper(&value); return 0;"
            )
            .is_err()
        );
    }
}

#[test]
fn valid_place_does_not_initialize_the_callers_object() {
    assert!(
        verify(
            "",
            "requires valid_place(p);",
            "int value; helper(&value); return value;"
        )
        .is_err()
    );
}

#[test]
fn valid_place_rejects_null_and_nonpointer_arguments() {
    assert!(verify("", "requires valid_place(p);", "helper(0); return 0;").is_err());
    for clause in ["requires valid_place(1);", "requires valid_place(p, p);"] {
        assert!(verify("", clause, "int value; helper(&value); return 0;").is_err());
    }
    assert!(parse("predicate valid_place(p: int32) { p == p }").is_err());
}
