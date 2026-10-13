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

#[test]
fn valid_place_prefix_checks_geometry_without_backing_access() {
    for count in [1, 8, 64, 1024] {
        let contract = format!("requires valid_place(p[0..{count}]);");
        let caller = format!("int values[{count}]; helper(values); return 0;");
        verify(&format!("int* end = p + {count};"), &contract, &caller).unwrap();
        assert!(verify("int value = *p;", &contract, &caller).is_err());
        assert!(verify("*p = 0;", &contract, &caller).is_err());
        let too_short = "int value; helper(&value); return 0;";
        if count > 1 {
            assert!(verify("", &contract, too_short).is_err());
        }
    }
}

#[test]
fn valid_place_empty_prefix_grants_no_object_or_formation() {
    verify("", "requires valid_place(p[0..0]);", "helper(0); return 0;").unwrap();
    for body in ["int* q = p + 0;", "int value = *p;", "*p = 0;"] {
        assert!(
            verify(
                body,
                "requires valid_place(p[0..0]);",
                "helper(0); return 0;"
            )
            .is_err()
        );
    }
    assert!(verify("", "requires valid_place(p[0..1]);", "helper(0); return 0;").is_err());
}

#[test]
fn valid_place_prefix_refuses_unsupported_bounds_and_preserves_initialization() {
    for clause in [
        "requires valid_place(p[1..2]);",
        "requires valid_place(p[0..-1]);",
        "requires valid_place(p[0..18446744073709551615u64]);",
        "requires valid_place(p[0..p]);",
        "requires valid_place(p[0]);",
    ] {
        assert!(
            verify("", clause, "int values[2]; helper(values); return 0;").is_err(),
            "{clause}"
        );
    }
    assert!(
        verify(
            "",
            "requires valid_place(p[0..1]);",
            "int value; helper(&value); return value;"
        )
        .is_err()
    );
}
