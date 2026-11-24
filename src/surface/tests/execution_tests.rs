use super::*;

fn generic_result_type_fixture() -> (&'static str, &'static str) {
    let c_source = r#"
        struct node { int32 value; };
        struct other { int32 value; };
        struct node* unchanged(struct node* p, struct other* q) { return p; }
    "#;
    // Null satisfies the logical pointer domain without assuming original
    // object-class evidence from a C formal's declared type.
    let source = r#"
        function select<T>(first: T, second: T) -> T { first }
        verifying "result.c";
        struct node* unchanged(struct node* p, struct other* q) {
            requires p == 0;
            ensures select(p, result) == p;
            ensures result == p;
        } by {
            step_until(function.exit);
            have select(p, result) == p by {
                unfold(select(p, result));
                close();
            }
            close();
        }
    "#;
    (source, c_source)
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_00")]
fn generic_function_keeps_the_declared_struct_pointer_result_type() {
    let (source, c_source) = generic_result_type_fixture();
    verify_c_sources(source, &[("result.c", c_source)])
        .expect("generic arguments retain the result's declared struct identity");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_00")]
fn generic_result_type_does_not_unify_distinct_structs() {
    let (source, c_source) = generic_result_type_fixture();
    let error = verify_c_sources(
        &source.replace("select(p, result)", "select(p, q)"),
        &[("result.c", c_source)],
    )
    .expect_err("distinct struct pointers cannot instantiate the same type parameter");
    assert!(error.message().contains("type parameter `T`"), "{error}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_00")]
fn generic_result_type_cannot_prove_a_false_postcondition() {
    let (source, c_source) = generic_result_type_fixture();
    verify_c_sources(
        &source.replace("ensures result == p", "ensures result != p"),
        &[("result.c", c_source)],
    )
    .expect_err("declared result metadata cannot prove a false postcondition");
}
use crate::kernel::LoopEffectOrigin;

fn authority_stack_project(click_source: &str) -> ClickProject {
    ClickProject::new(
        "authority_stack.click",
        [ClickModuleSource::new(
            "authority_stack.click",
            click_source,
            [],
        )],
    )
    .with_c_profile(CProjectProfile {
        target: None,
        runtime: None,
    })
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_00")]
fn authority_establishes_and_retires_empty_stack_population() {
    let c_source = r#"
        int32 value(void) {
            int32 x = 7;
            return x;
        }
    "#;
    let click_source = r#"
        authorized abstract resource reference(p: int32*);
        verifying "authority_stack.c";

        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(authority(reference(&x)));
            unfold(authority(reference(&x)));
            step_until(function.exit);
            close();
        }
    "#;
    parser::parse_file_items(click_source)
        .expect("the source fold/unfold fixture must parse independently of mode gating");
    verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect("the creator may establish and retire one empty population");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_01")]
fn authority_conserves_one_local_member() {
    let c_source = r#"
        int32 value(void) {
            int32 x = 7;
            return x;
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        verifying "authority_stack.c";

        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(authority(reference(&x)));
            have count(reference(&x)) == 0 by { close(); }
            fold(reference(&x));
            have count(reference(&x)) == 1 by { close(); }
            unfold(reference(&x));
            have count(reference(&x)) == 0 by { close(); }
            unfold(authority(reference(&x)));
            step_until(function.exit);
            close();
        }
    "#;
    verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect("one checked member changes count from zero to one and back");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_01")]
fn authority_cannot_reestablish_after_retirement() {
    let c_source = r#"
        int32 value(void) {
            int32 x = 7;
            return x;
        }
    "#;
    let click_source = r#"
        authorized abstract resource reference(p: int32*);
        verifying "authority_stack.c";

        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(authority(reference(&x)));
            unfold(authority(reference(&x)));
            fold(authority(reference(&x)));
            step_until(function.exit);
            close();
        }
    "#;
    let error = verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("a retired population cannot be established a second time");
    assert!(
        error.message().contains("cannot be established again"),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_01")]
fn authority_rejects_automatic_storage_end_with_live_authority() {
    let c_source = r#"
        int32 value(void) {
            int32 x = 7;
            return x;
        }
    "#;
    let click_source = r#"
        authorized abstract resource reference(p: int32*);
        verifying "authority_stack.c";

        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(authority(reference(&x)));
            step_until(function.exit);
            close();
        }
    "#;
    let error = verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("automatic storage cannot end while its authority remains live");
    assert!(error.message().contains("authority"), "{error:?}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_01")]
fn authority_imported_pointer_without_live_storage_cannot_establish_population() {
    let c_source = r#"
        int32 value(int32* p) {
            return 7;
        }
    "#;
    let click_source = r#"
        authorized abstract resource reference(p: int32*);
        verifying "authority_stack.c";

        int32 value(int32* p) {
            owns p[0..1];
            ensures result == 7;
        } by {
            fold(authority(reference(p)));
            step_until(function.exit);
            close();
        }
    "#;
    let error = verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("an imported pointer without live base storage cannot establish authority");
    assert!(
        error.message().contains("Requires live base storage"),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_02")]
fn authority_cannot_create_untracked_member_before_establishment() {
    let c_source = r#"
        int32 value(void) {
            int32 x = 7;
            return x;
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        verifying "authority_stack.c";

        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(reference(&x));
            fold(authority(reference(&x)));
            step_until(function.exit);
            close();
        }
    "#;
    let error = verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("a member cannot be born before matching authority is held");
    assert!(
        error
            .message()
            .contains("Requires owns authority(reference(p))"),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_02")]
fn authority_rejects_double_member_consumption() {
    let c_source = "int32 value(void) { int32 x = 7; return x; }";
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        verifying "authority_stack.c";

        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(authority(reference(&x)));
            fold(reference(&x));
            unfold(reference(&x));
            unfold(reference(&x));
            unfold(authority(reference(&x)));
            step_until(function.exit);
            close();
        }
    "#;
    let error = verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("one member cannot be consumed twice");
    assert!(
        error.message().contains("Requires owns reference(p)"),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_02")]
fn authority_cannot_retire_with_live_member() {
    let c_source = "int32 value(void) { int32 x = 7; return x; }";
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        verifying "authority_stack.c";

        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(authority(reference(&x)));
            fold(reference(&x));
            unfold(authority(reference(&x)));
            step_until(function.exit);
            close();
        }
    "#;
    let error = verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("retirement requires an empty population");
    assert!(
        error
            .message()
            .contains("members of the population are still outstanding"),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_02")]
fn authority_count_requires_owned_authority() {
    let c_source = "int32 value(int32* p) { return 7; }";
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        verifying "authority_stack.c";

        int32 value(int32* p) {
            owns p[0..1];
            ensures result == 7;
        } by {
            have count(reference(p)) == 0 by { close(); }
            step_until(function.exit);
            close();
        }
    "#;
    let error = verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("zero is not observable without matching authority");
    assert!(error.message().contains("authority"), "{error:?}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_03")]
fn authority_count_of_a_population_without_authority_is_refused() {
    let c_source = "int32 value(int32* p) { return 7; }";
    let click_source = r#"
        authorized abstract resource reference(p: int32*);
        verifying "authority_stack.c";

        int32 value(int32* p) {
            ensures count(reference(p)) == 0;
        }
    "#;
    let error = verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("a count needs the population's authority");
    assert!(error.message().contains("count"), "{error:?}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_03")]
fn authority_plain_c_helper_call_follows_the_ordinary_call_rules() {
    let c_source = r#"
        int32 helper(void) { return 7; }
        int32 value(void) {
            int32 x = helper();
            return x;
        }
    "#;
    let click_source = r#"
        verifying "authority_stack.c";

        int32 value() {
            ensures result == 7;
        }
    "#;
    let error = verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("an unverified helper without a contract cannot be called opaquely");
    // The helper's contract moves no resource, so population rules add no
    // refusal of its own; the ordinary rule for unverified callees applies.
    assert!(
        error
            .message()
            .contains("the sidecar states no contract for it"),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_03")]
fn authority_calls_a_verified_helper_without_population_effects() {
    let c_source = r#"
        int32 helper(void) { return 7; }
        int32 value(void) { return helper(); }
    "#;
    let click_source = r#"
        verifying "authority_stack.c";

        int32 helper() {
            ensures result == 7;
        }

        int32 value() {
            ensures result == 7;
        }
    "#;
    verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect("an independently verified helper preserves an untouched population ledger");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_03")]
fn authority_helper_returns_the_same_authority_and_member() {
    let c_source = r#"
        int32 helper(int32* p) { return 7; }
        int32 value(void) {
            int32 x = 7;
            int32 result = helper(&x);
            return result;
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        verifying "authority_stack.c";

        int32 helper(int32* p) {
            owns authority(reference(p));
            owns reference(p);
            ensures result == 7;
        }

        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(authority(reference(&x)));
            fold(reference(&x));
            step();
            step();
            step();
            unfold(reference(&x));
            unfold(authority(reference(&x)));
            step_until(function.exit);
            close();
        }
    "#;
    verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect("a verified helper returns the exact authority and member it received");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_04")]
fn authority_helper_consumes_one_member_and_returns_authority() {
    let c_source = r#"
        int32 drop_reference(int32* p) { return 7; }
        int32 value(void) {
            int32 x = 7;
            int32 result = drop_reference(&x);
            return result;
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        verifying "authority_stack.c";

        int32 drop_reference(int32* p) {
            owns authority(reference(p));
            consumes reference(p);
            ensures result == 7;
        } by {
            unfold(reference(p));
            step_until(function.exit);
            close();
        }

        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(authority(reference(&x)));
            fold(reference(&x));
            step();
            step();
            step();
            have count(reference(&x)) == 0 by { close(); }
            unfold(authority(reference(&x)));
            step_until(function.exit);
            close();
        }
    "#;
    verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect("a verified helper consumes one owned member and returns authority");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_04")]
fn authority_helper_produces_one_member_and_returns_authority() {
    let c_source = r#"
        int32 add_reference(int32* p) { return 7; }
        int32 value(void) {
            int32 x = 7;
            int32 result = add_reference(&x);
            return result;
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        verifying "authority_stack.c";

        int32 add_reference(int32* p) {
            owns authority(reference(p));
            produces reference(p);
            ensures result == 7;
        } by {
            fold(reference(p));
            step_until(function.exit);
            close();
        }

        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(authority(reference(&x)));
            step();
            step();
            step();
            have count(reference(&x)) == 1 by { close(); }
            unfold(reference(&x));
            unfold(authority(reference(&x)));
            step_until(function.exit);
            close();
        }
    "#;
    verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect("a verified helper creates one owned member and returns authority");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_04")]
fn authority_helper_cannot_claim_creation_without_folding_member() {
    let c_source = r#"int32 add_reference(int32* p) { return 7; }"#;
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        verifying "authority_stack.c";
        int32 add_reference(int32* p) {
            owns authority(reference(p));
            produces reference(p);
            ensures result == 7;
        }
    "#;
    let error = verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("a declared production needs a checked member birth in the helper proof");
    assert!(
        error.message().contains("Requires produces reference(p)"),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_04")]
fn authority_helper_cannot_birth_imported_member_twice() {
    let c_source = r#"int32 add_reference(int32* p) { return 7; }"#;
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        verifying "authority_stack.c";
        int32 add_reference(int32* p) {
            owns authority(reference(p));
            produces reference(p);
            ensures result == 7;
        } by {
            fold(reference(p));
            fold(reference(p));
            step_until(function.exit);
            close();
        }
    "#;
    let error = verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("one helper proof cannot create two members");
    assert!(error.message().contains("reference"), "{error:?}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_05")]
fn authority_creating_helper_requires_caller_authority() {
    let c_source = r#"
        int32 add_reference(int32* p) { return 7; }
        int32 value(void) {
            int32 x = 7;
            return add_reference(&x);
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        verifying "authority_stack.c";
        int32 add_reference(int32* p) {
            owns authority(reference(p));
            produces reference(p);
            ensures result == 7;
        } by {
            fold(reference(p));
            step_until(function.exit);
            close();
        }
        int32 value() {
            ensures result == 7;
        }
    "#;
    let error = verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("a helper cannot create a member without concrete caller authority");
    assert!(error.message().contains("authority"), "{error:?}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_05")]
fn authority_helper_cannot_create_private_memory_from_opaque_authority() {
    let c_source = r#"int32 add_reference(int32* p) { return 7; }"#;
    let click_source = r#"
        authorized resource reference(p: int32*) { owns p[0..1]; }
        verifying "authority_stack.c";
        int32 add_reference(int32* p) {
            owns authority(reference(p));
            produces reference(p);
            ensures result == 7;
        } by {
            fold(reference(p));
            step_until(function.exit);
            close();
        }
    "#;
    let error = verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("opaque authority alone cannot supply a member's private memory");
    assert!(
        error.message().contains("reference") || error.message().contains("member"),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_05")]
fn authority_helper_cannot_claim_consumption_without_spending_member() {
    let c_source = r#"int32 drop_reference(int32* p) { return 7; }"#;
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        verifying "authority_stack.c";
        int32 drop_reference(int32* p) {
            owns authority(reference(p));
            consumes reference(p);
            ensures result == 7;
        }
    "#;
    let error = verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("a declared consume needs a checked member death in the helper proof");
    assert!(error.message().contains("reference"), "{error:?}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_05")]
fn authority_helper_cannot_spend_imported_member_twice() {
    let c_source = r#"int32 drop_reference(int32* p) { return 7; }"#;
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        verifying "authority_stack.c";
        int32 drop_reference(int32* p) {
            owns authority(reference(p));
            consumes reference(p);
            ensures result == 7;
        } by {
            unfold(reference(p));
            unfold(reference(p));
            step_until(function.exit);
            close();
        }
    "#;
    let error = verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("one imported member cannot be consumed twice");
    assert!(error.message().contains("reference"), "{error:?}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_06")]
fn authority_consuming_helper_requires_caller_member() {
    let c_source = r#"
        int32 drop_reference(int32* p) { return 7; }
        int32 value(void) {
            int32 x = 7;
            return drop_reference(&x);
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        verifying "authority_stack.c";
        int32 drop_reference(int32* p) {
            owns authority(reference(p));
            consumes reference(p);
            ensures result == 7;
        } by {
            unfold(reference(p));
            step_until(function.exit);
            close();
        }
        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(authority(reference(&x)));
            step_until(function.exit);
            close();
        }
    "#;
    let error = verify_c_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("authority alone cannot supply a member consumed by a helper");
    assert!(error.message().contains("reference"), "{error:?}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_06")]
fn verifies_loadable_segment_proposition_for_indexed_read() {
    let c_source = r#"
            int32 read_index(int32 p[], int32 index, int32 n) {
                return p[index];
            }
        "#;
    let click_source = r#"
            verifying "read_index.c";

            int32 read_index(int32 p[], int32 index, int32 n) {
                requires 0 <= index;
                requires index < n;
                views p[0..n];

                ensures returns_loaded_value: result == p[index];
            }
        "#;

    let verified = verify_c_sources(click_source, &[("read_index.c", c_source)])
        .expect("viewable segment should prove indexed read viewability");

    assert_eq!(verified.len(), 1);
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_06")]
fn bounded_assignment_preserves_successor_definedness() {
    let c_source = r#"
            int32 add_twice(int32 x) {
                int32 first;
                first = x + 1;
                return first + 1;
            }
        "#;
    let click_source = r#"
            verifying "add_twice.c";

            int32 add_twice(int32 x) {
                requires x >= 0;
                requires x <= 2147483645;
                ensures to_integer(result) == to_integer((x + 1) + 1);
            }
        "#;

    verify_c_sources(click_source, &[("add_twice.c", c_source)])
        .expect("the bound on x should prove both additions defined");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_06")]
fn uninitialized_scalar_read_fails_verification() {
    let c_source = r#"
            int32 read_uninitialized() {
                int32 x;
                return x;
            }
        "#;
    let click_source = r#"
            verifying "read_uninitialized.c";

            int32 read_uninitialized() {
                ensures result == 0;
            }
        "#;

    let error = verify_c_sources(click_source, &[("read_uninitialized.c", c_source)])
        .expect_err("an uninitialized scalar read must not verify");
    assert!(
        error.message().contains("read of uninitialized storage"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_07")]
fn uninitialized_local_array_read_fails_verification() {
    let c_source = r#"
            int32 read_uninitialized_array() {
                int32 data[1];
                return data[0];
            }
        "#;
    let click_source = r#"
            verifying "read_uninitialized_array.c";

            int32 read_uninitialized_array() {
                ensures result == 0;
            }
        "#;

    let error = verify_c_sources(click_source, &[("read_uninitialized_array.c", c_source)])
        .expect_err("an uninitialized local array read must not verify");
    assert!(
        error.message().contains("read of uninitialized storage"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_07")]
fn pointer_argument_keeps_its_null_execution_path() {
    let c_source = r#"
            int32 pointer_is_null(int32* p) {
                if (p == 0) {
                    return 1;
                }
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "pointer_is_null.c";

            int32 pointer_is_null(int32* p) {
                ensures result == 0;
            }
        "#;

    verify_c_sources(click_source, &[("pointer_is_null.c", c_source)])
        .expect_err("an unconstrained pointer parameter may be null");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_07")]
fn step_and_execute_step_advance_one_concrete_loop_transition() {
    let c_source = r#"
            int32 count_two() {
                int32 i;
                i = 0;
                while (i < 2) {
                    i = i + 1;
                }
                return i;
            }
        "#;
    let click_source = r#"
            verifying "count_two.c";

            int32 count_two() {
                ensures returns_two: result == 2 by {
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    close();
                }
            }
        "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    let verified = verify_c_sources(click_source, &[("count_two.c", c_source)])
        .expect("small tactics should traverse concrete loop heads and iterations");

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].proof_kind(), ProofKind::TacticScript);
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "a concrete loop trace should complete without rerunning the function body"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_07")]
fn early_return_completes_without_a_body_rerun() {
    let c_source = r#"
            int32 clamp(int32 x) {
                if (x < 0) {
                    return 0;
                }
                return x;
            }
        "#;
    let click_source = r#"
            verifying "clamp.c";

            int32 clamp(int32 x) {
                ensures result >= 0;
            }
        "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c_sources(click_source, &[("clamp.c", c_source)])
        .expect("an early return should verify from its retained statement theorems");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "a path that returns before the end of the body should complete without rerunning it"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_08")]
fn symbolic_loop_bound_invariant_completes_without_a_body_rerun() {
    let c_source = r#"
            int32 count_to_n(int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    i = i + 1;
                }
                return i;
            }
        "#;
    let click_source = r#"
            verifying "count_to_n.c";

            int32 count_to_n(int32 n) {
                requires n >= 0 and n <= 2147483647;
                ensures result == n;
            } by {
                step();
                step();
                loop {
                    decreases n - i;
                    invariant i >= 0 and i <= n;
                }
                step();
                close();
            }
        "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c_sources(click_source, &[("count_to_n.c", c_source)])
        .expect("a symbolic loop bound with a conjunctive invariant should verify");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "the invariant conjuncts the loop theorem assumed are retained by the loop step"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_08")]
fn malloc_null_check_completes_without_a_body_rerun() {
    let c_source = r#"
            struct item {
                int32 value;
            };

            int32 alloc_then_free() {
                struct item* item = malloc(sizeof(struct item));
                if (item == 0) {
                    return -1;
                }
                item->value = 7;
                free(item);
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "alloc_then_free.c";

            int32 alloc_then_free() {
                ensures result == -1 or result == 0;
            }
        "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c_sources(click_source, &[("alloc_then_free.c", c_source)])
        .expect("a null-checked allocation that is freed should verify");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "the null check resolves the pending allocation in the reached state as it does in execution"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_08")]
fn post_execution_case_split_completes_without_a_body_rerun() {
    let c_source = r#"
            int32 clamp_positive(int32 a) {
                if (a > 0) {
                    return a;
                }
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "clamp_positive.c";

            int32 clamp_positive(int32 a) {
                ensures result >= 0;
            } by {
                if a > 0 {
                    step_until(function.exit);
                    close();
                } else {
                    step_until(function.exit);
                    close();
                }
            }
        "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c_sources(click_source, &[("clamp_positive.c", c_source)])
        .expect("a post-execution case split should verify");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "forked outcome paths carry forked traces with their case arms"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_08")]
fn have_after_loop_completes_without_a_body_rerun() {
    let c_source = r#"
            int32 count_then_add() {
                int32 i;
                int32 j;
                i = 0;
                while (i < 1) {
                    i = i + 1;
                }
                j = 0;
                while (j < 1) {
                    j = j + 1;
                }
                return i + j;
            }
        "#;
    let click_source = r#"
            verifying "count_then_add.c";

            int32 count_then_add() {
                ensures result == 2;
            } by {
                step();
                step();
                step();
                loop {
                    decreases 1 - i;
                    invariant i >= 0 and i <= 1;
                }
                step();
                loop {
                    decreases 1 - j;
                    invariant j >= 0 and j <= 1;
                }
                have i == 1 by close();
                have j == 1 by close();
                step();
                close();
            }
        "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c_sources(click_source, &[("count_then_add.c", c_source)])
        .expect("facts established by `have` after the loops should verify the return");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "the return statement's theorem lists the `have` facts; the retained context vouches for them"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_09")]
fn applied_user_theorem_completes_without_a_body_rerun() {
    let c_source = r#"
            int32 increment(int32 x) {
                return x + 1;
            }
        "#;
    let click_source = r#"
            verifying "increment.c";

            theorem increment_is_defined(x: int32) {
                requires x < 2147483647;

                ensures defined(x + 1) by {
                    close();
                }
            }

            int32 increment(int32 x) {
                requires x < 2147483647;
                ensures to_integer(result) == to_integer(x + 1);
            } by {
                apply(increment_is_defined(x));
                step();
                close();
            }
        "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c_sources(click_source, &[("increment.c", c_source)])
        .expect("an applied user theorem should discharge the step's definedness");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "the applied theorem's fact is in the context the step was proved under"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_09")]
fn verified_loop_summary_completes_without_a_body_rerun() {
    let c_source = r#"
            int32 count_to_three() {
                int32 i;
                i = 0;
                while (i < 3) {
                    i = i + 1;
                }
                return i;
            }
        "#;
    let click_source = r#"
            verifying "count_to_three.c";

            int32 count_to_three() {
                ensures result == 3;
            } by {
                step();
                step();
                have i == 0 by {
                    close();
                }
                loop {
                    decreases 3 - i;
                    invariant i >= 0;
                    invariant i <= 3;
                }
                step();
                close();
            }
        "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c_sources(click_source, &[("count_to_three.c", c_source)])
        .expect("verified loop summary should retain its checked statement theorem");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "a verified loop summary should complete without rerunning the function body"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_09")]
fn linear_execute_checks_the_branch_arm_refusal_program() {
    let markdown =
        include_str!("../../../mdtests/execute_branch_arm_stops_at_shared_continuation.md");
    let mdtest = crate::cli::parse_mdtest(std::path::Path::new("branch-arm.md"), markdown).unwrap();
    let source = mdtest.click_source.as_deref().unwrap();
    let linear = source.replace(
        "    branch {\n        true => {\n            step();\n            step();\n        }\n        false => {}\n    }\n",
        "",
    );
    assert_ne!(
        linear, source,
        "the control must replace the explicit branch"
    );
    let sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c_sources(&linear, &sources)
        .expect("the implicit tail may follow the same C arms into their continuation");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_09")]
fn execute_in_loop_preservation_keeps_the_function_exit_miss() {
    let c = "void countdown(int32 more) { while (more > 0) { more = more - 1; } }";
    let source = r#"
        verifying "countdown.c";
        void countdown(int32 more) {
            requires 0 <= more;
            ensures 1 == 1;
        } by {
            loop {
                decreases more;
                invariant 0 <= more;
                initialize by close();
                maintain by { step_until(function.exit); }
            }
            step_until(function.exit);
        }
    "#;
    let error = verify_c_sources(source, &[("countdown.c", c)])
        .expect_err("a loop preservation region cannot execute to function exit");
    assert!(
        error
            .message()
            .contains("`step_until` found no checked step from this frontier"),
        "{}",
        error.message()
    );
    assert!(!error.message().contains("an arm of `branch`"));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_10")]
fn bounded_execute_resumes_and_explores_symbolic_branches() {
    let c_source = r#"
            int32 choose_after_init(int32 x) {
                int32 y;
                y = 0;
                if (x > 0) {
                    y = 1;
                } else {
                    y = 2;
                }
                return y;
            }
        "#;
    let click_source = r#"
            verifying "choose_after_init.c";

            int32 choose_after_init(int32 x) {
                ensures result == 1 or result == 2 by {
                    step();
                    step();
                }
            }
        "#;

    let verified = verify_c_sources(click_source, &[("choose_after_init.c", c_source)])
        .expect("bounded execution should resume and prove every symbolic branch");

    assert_eq!(verified.len(), 2);
    assert!(
        verified
            .iter()
            .all(|theorem| theorem.proof_kind() == ProofKind::TacticScript)
    );
    for theorem in &verified {
        let expanded = theorem.expanded_proof_tactics().unwrap_or_else(|| {
            panic!(
                "bounded branch execution should expand: {:?}",
                theorem.expansion_blocker()
            )
        });
        let proof_if = expanded
            .iter()
            .find_map(|tactic| match tactic {
                ProofTactic::If(proof_if) => Some(proof_if),
                _ => None,
            })
            .expect("bounded branch execution should retain its surface branch");
        assert_eq!(proof_if.then_tactics.last(), Some(&ProofTactic::Known));
        assert_eq!(proof_if.else_tactics.last(), Some(&ProofTactic::Known));
        ProofCertificate::from_proof_tactics(&expanded)
            .expect("bounded branch expansion should be a surface certificate");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_10")]
fn verifies_fill3_c_source_with_sidecar_specification() {
    let verified = verify_c_sources(FILL3_CLICK, &[("fill3.c", FILL3_C)])
        .expect("fill3 sidecar should verify");

    assert_eq!(verified.len(), 1);
    let verified = &verified[0];
    let crate::kernel::ProgramExpression::Value(crate::kernel::ProgramValue::Pointer(argument)) =
        &verified.specification.arguments()[0]
    else {
        panic!("fill3's input is a pointer");
    };
    let base = argument.address().clone();
    let first = base.clone();
    let second = offset_pointer_by_int32_elements(base.clone(), MachineTerm::constant(1));
    let third = offset_pointer_by_int32_elements(base.clone(), MachineTerm::constant(2));
    let local_i_block = crate::kernel::AddressBase::AutomaticLocal {
        binding: crate::kernel::LocalBindingId::new(
            crate::kernel::LocalFunctionId::new(Some("fill3.c".into()), "fill3".into()),
            false,
            0,
            Some("i".into()),
        ),
        instance: crate::kernel::LocalStorageInstance::Implicit,
    };
    let local_i = Address {
        base: local_i_block.clone(),
        offset: AddressOffset::Constant(0),
    };
    let entry = verified
        .specification
        .state()
        .program_point()
        .entry_cell_version(&base, ProgramType::Int32)
        .expect("the initial array names its function-entry version");
    let initial_memory = memory_with_symbolic_loadable_cells(
        SymbolicMemory::new(),
        &entry,
        &std::collections::BTreeMap::from([(
            "p".to_string(),
            ConcreteMemoryRangeSeed {
                base: base.clone(),
                bytes: 12,
                element_width: 4,
                element_type: Some(ProgramType::Int32),
                struct_layout: None,
            },
        )]),
    );
    let initial_resources =
        ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
            base.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(3),
        )));
    let final_memory = initial_memory
        .clone()
        .with_block(local_i_block.clone(), 4)
        .store(first, int32(0))
        .store(second, int32(1))
        .store(third, int32(2))
        .store(local_i, int32(3))
        .without_local_block(&local_i_block);

    // The entry has a creation ledger with a fresh
    // identity; it records nothing here.
    assert!(
        verified
            .specification
            .state()
            .equal_up_to_unused_creation_ledgers(
                &ExecutionState::new()
                    .with_population_creation_tracking()
                    .with_memory(initial_memory)
                    .with_resource_context(initial_resources.clone())
            )
    );
    assert_eq!(
        verified.specification.arguments(),
        &[crate::kernel::program_expression::pointer_value(
            base.clone()
        )]
    );
    assert!(
        verified
            .specification
            .outcome()
            .equal_up_to_unused_creation_ledgers(&FunctionOutcome::Return {
                value: int32(2).into(),
                state: Box::new(
                    ExecutionState::new()
                        .with_population_creation_tracking()
                        .with_memory(final_memory)
                        .with_resource_context(initial_resources)
                ),
            })
    );
    let parsed_source = syntax::parse_functions_for_source(FILL3_C, "fill3.c")
        .unwrap()
        .remove(0);
    let parameter_binding = parsed_source.parameters()[0].binding_name().clone();
    assert_eq!(
        implication_body(verified.theorem.proposition()),
        &Proposition::ProgramFunctionPartiallySatisfiesSpecification {
            function: Box::new(
                {
                    let parsed = parsed_source.to_kernel_function();
                    let ProgramStatement::Seq(statements) = parsed.body().clone() else {
                        panic!("fill3 body should have a prefix and suffix");
                    };
                    let (prefix, suffix) = (statements.first().clone(), statements.rest());
                    let ProgramStatement::Seq(statements) = suffix.as_ref().clone() else {
                        panic!("fill3 suffix should contain the loop and return");
                    };
                    let (loop_statement, result) = (statements.first().clone(), statements.rest());
                    let ProgramStatement::Loop {
                        test,
                        invariant,
                        invariant_checks,
                        body,
                        ..
                    } = loop_statement.as_ref().clone()
                    else {
                        panic!("fill3 suffix should start with a loop");
                    };
                    let condition = test.source_condition().expect("pure fixture test").clone();
                    program_function(
                        ProgramType::Int32,
                        "fill3",
                        vec![
                            crate::kernel::program_parameter(
                                parameter_binding.clone(),
                                ProgramType::Int32Pointer,
                            )
                            .with_pointee_class(Some(
                                crate::kernel::effective_type::CAccessClass::Scalar(
                                    crate::kernel::effective_type::CScalarClass::Int,
                                ),
                            )),
                        ],
                        program_seq(
                            prefix.as_ref().clone(),
                            program_seq(
                                program_while_with_invariant_and_effect_checks(
                                    condition,
                                    invariant,
                                    invariant_checks,
                                    vec![
                                        // A resource-derived frame is lowered without
                                        // segments; the kernel installs its ranges from
                                        // the checked entry transition.
                                        LoopEffectCheck::new_with_origin(
                                            LoopEffect::Mutable(Vec::new()),
                                            LoopEffectSpan::Whole,
                                            LoopEffectOrigin::InheritedResourceDerived,
                                            Some(
                                                "loop 0 inherited owned resource frame".to_string(),
                                            ),
                                        )
                                        .with_validated_ranges(vec![MemoryRange::new(
                                            base.clone(),
                                            MachineTerm::constant(0),
                                            MachineTerm::constant(3),
                                        )]),
                                    ],
                                    body.as_ref().clone(),
                                ),
                                result.as_ref().clone(),
                            ),
                        ),
                    )
                    .with_source_body(parsed.source_body().clone())
                }
                .with_resource_summary(
                    vec![ResourceSpec::memory(
                        MemorySegment::new(
                            ProgramExpression::Variable(("p".to_string()).into()),
                            ProgramExpression::Value(int32(0)),
                            ProgramExpression::Value(int32(3)),
                        ),
                        KernelResourceAccessMode::Own,
                        ResourceTransferRole::Consume,
                        ResourceStateSource::Entry,
                    )],
                    Vec::new(),
                )
                .with_contract(
                    vec![SpecProposition::MemoryLoadable {
                        point: SpecPoint::Current,
                        base: SpecExpression::ProgramExpression(ProgramExpression::Variable(
                            parameter_binding.clone(),
                        )),
                        start: SpecExpression::Value(int32(0)),
                        end: SpecExpression::Value(int32(3)),
                        element_width: 4,
                    }],
                    vec![SpecProposition::Comparison {
                        left: SpecExpression::ProgramExpression(ProgramExpression::Variable(
                            crate::kernel::CONTRACT_RESULT,
                        )),
                        operator: KernelComparisonOperator::Equal,
                        right: SpecExpression::Value(int32(2)),
                    }],
                    // The write footprint is not lowered: the kernel projects it
                    // from the resource clause, so the explicit list stays empty.
                    Vec::new(),
                    vec![FunctionContractClaim::ensure_proposition(0, 0)],
                    true,
                )
                .with_resource_derived_mutable_frame()
            ),
            specification: Box::new(verified.specification.clone()),
        }
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_10")]
fn bounded_solve_loop_expands_without_a_detached_summary() {
    let sources = [("fill3.c", FILL3_C)];
    let position = c_tactic_source_position(FILL3_CLICK, &sources, "fill3.returns_second", 0)
        .expect("the default solve proof should have a source position");
    let expanded = expand_c_tactic_source_at(FILL3_CLICK, &sources, position.line, position.column)
        .expect("bounded loop execution should have a surface certificate");

    assert!(!expanded.contains("summarize("), "{expanded}");
    verify_c_sources(&expanded, &sources)
        .expect("the bounded loop certificate should freshly check");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_10")]
fn signature_mismatch_reports_direct_error() {
    let source = FILL3_CLICK.replace("int32* p", "int32 q");
    let error = verify_c_sources(&source, &[("fill3.c", FILL3_C)])
        .expect_err("wrong signature should fail");

    assert!(
        error.message().contains("signature mismatch"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_11")]
fn pointer_constness_signature_mismatch_displays_both_qualifiers() {
    for (pointer_type, rendered_type) in [
        ("struct Value*", "struct Value*"),
        ("int32*", "Int32Pointer"),
    ] {
        for (click_const, c_const) in [("", "const "), ("const ", "")] {
            let c_source = format!(
                "struct Value {{ int32 value; }}; int32 read({c_const}{pointer_type} self) {{ return 0; }}"
            );
            let click_source = format!(
                "verifying \"read.c\"; int32 read({click_const}{pointer_type} self) {{ ensures result == 0; }}"
            );
            let error = verify_c_sources(&click_source, &[("read.c", &c_source)])
                .expect_err("different pointee qualifiers must still fail signature checking");
            assert_eq!(error.kind(), ClickErrorKind::Type);
            assert!(
                error.message().contains(&format!(
                    ".click has {click_const}{rendered_type} self, C has {c_const}{rendered_type} self"
                )),
                "{}",
                error.message()
            );
        }
        for qualifier in ["", "const "] {
            let c_source = format!(
                "struct Value {{ int32 value; }}; int32 read({qualifier}{pointer_type} self) {{ return 0; }}"
            );
            let click_source = format!(
                "verifying \"read.c\"; int32 read({qualifier}{pointer_type} self) {{ ensures result == 0; }}"
            );
            verify_c_sources(&click_source, &[("read.c", &c_source)])
                .expect("matching pointee qualifiers must still verify");
        }
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_11")]
fn struct_name_signature_mismatch_reports_direct_error() {
    let c_source = r#"
        struct actual {
            int32 value;
        };

        struct expected {
            int32 value;
        };

        int32 get_value(struct actual* p) {
            return p->value;
        }
    "#;
    let click_source = r#"
        verifying "get_value.c";

        int32 get_value(struct expected* p) {
            views p->value;
            ensures result == old(p->value);
        }
    "#;

    let error = verify_c_sources(click_source, &[("get_value.c", c_source)])
        .expect_err("wrong struct name should fail");

    assert!(
        error.message().contains(
            "signature mismatch for `get_value` parameter 1 in `get_value.c`: .click has struct expected* p, C has struct actual* p"
        ),
        "{}",
        error.message()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.2s in the parallel gate"]
fn observed_cursor_facts_produce_checkable_surface_certificates() {
    let c_source = r#"
        struct input_cursor {
            int32 pos;
            int32 len;
            int32* data;
        };

        int32 input_cursor_peek(struct input_cursor* owner) {
            return owner->data[owner->pos];
        }
    "#;
    let take_c_source = r#"
        struct input_cursor {
            int32 pos;
            int32 len;
            int32* data;
        };

        int32 input_cursor_take(struct input_cursor* owner) {
            int32 value;
            value = owner->data[owner->pos];
            owner->pos = owner->pos + 1;
            return value;
        }
    "#;
    let click_source = r#"
        resource readable_input(data: int32*, length: int32) {
            views data[0..length];
            fact 0 <= length;
        }

        resource input_cursor(owner: struct input_cursor*) {
            owns owner->pos;
            owns owner->len;
            owns owner->data;
            views readable_input(owner->data, owner->len);
            fact 0 <= owner->pos;
            fact owner->pos <= owner->len;
            fact separate(
                memory(*owner),
                memory(owner->data[0..owner->len])
            );
        }

        verifying "input_cursor_peek.c";
        verifying "input_cursor_take.c";

        int32 input_cursor_peek(struct input_cursor* owner) {
            requires owner->pos < owner->len;
            views input_cursor(owner);
            ensures result == owner->data[owner->pos];
        } by {
            observe(input_cursor(owner));
            observe(readable_input(owner->data, owner->len));
            step_until(function.exit);
            close();
        }

        int32 input_cursor_take(struct input_cursor* owner) {
            requires owner->pos < owner->len;
            owns input_cursor(owner);
            ensures result == old(owner->data[owner->pos]);
            ensures owner->pos == old(owner->pos) + 1;
            ensures owner->len == old(owner->len);
            ensures owner->data == old(owner->data);
        } by {
            unfold(input_cursor(owner));
            observe(readable_input(owner->data, owner->len));
            step_until(function.exit);
            have 0 <= owner->pos by close();
            have owner->pos <= owner->len by close();
            have separate(
                memory(*owner),
                memory(owner->data[0..owner->len])
            ) by {
                close();
            }
            fold(input_cursor(owner));
            close();
        }

    "#;

    let sources = [
        ("input_cursor_peek.c", c_source),
        ("input_cursor_take.c", take_c_source),
    ];
    let final_solve = click_source
        .rfind("close();")
        .expect("final solve should exist");
    let position = expansion::position_at_offset(click_source, final_solve);
    let expanded =
        expand_c_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("the grouped solve should emit a non-circular surface certificate");
    verify_c_sources(&expanded, &sources)
        .expect("the grouped solve surface certificate should check from fresh source");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2s in the parallel gate"]
fn explicit_store_step_with_unfolded_resource_facts_verifies() {
    let c_source = r#"
        struct owned_string {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 owned_string_set(
            struct owned_string* owner,
            int32 index,
            int32 value
        ) {
            owner->data[index] = value;
            return value;
        }
    "#;
    let click_source = r#"
        predicate terminated_at(data: int32[], length: int32) {
            data[length] == 0
        }

        resource owned_string(owner: struct owned_string*) {
            owns owner->len;
            owns owner->cap;
            owns owner->data;
            owns owner->data[0..owner->cap];
            fact 0 <= owner->len;
            fact owner->len < owner->cap;
            fact terminated_at(owner->data, owner->len);
            fact separate(
                memory(*owner),
                memory(owner->data[0..owner->cap])
            );
        }

        verifying "owned_string_set.c";

        int32 owned_string_set(
            struct owned_string* owner,
            int32 index,
            int32 value
        ) {
            requires 0 <= index;
            requires index < owner->len;
            owns owned_string(owner);
            ensures result == value;
            ensures owner->data[index] == value;
        } by {
            unfold(owned_string(owner));
            unfold(terminated_at(owner->data, owner->len));
            step();
            have terminated_at(owner->data, owner->len) by {
                unfold(terminated_at(owner->data, owner->len));
                close();
            }
            have owner->data[owner->len] == 0 by close();
            have 0 <= owner->len by close();
            have owner->len < owner->cap by close();
            have separate(
                memory(*owner),
                memory(owner->data[0..owner->cap])
            ) by {
                close();
            }
            fold(owned_string(owner));
            step();
            close();
        }
    "#;

    let (verified, _events) = crate::instrumentation::collect(|| {
        verify_c_sources(click_source, &[("owned_string_set.c", c_source)])
    });
    verified.expect("explicit store certificate should verify");

    let smart_step = click_source
        .rfind("step();")
        .expect("the resource-backed return step should be present");
    let position = expansion::position_at_offset(click_source, smart_step);
    let expanded = expand_c_tactic_source_at(
        click_source,
        &[("owned_string_set.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained Have and statement step should expand");
    assert!(expanded.contains("have "), "{expanded}");
    assert!(expanded.contains("step();"), "{expanded}");
    verify_c_sources(&expanded, &[("owned_string_set.c", c_source)])
        .expect("the rewritten resource-backed step should verify normally");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3.0s in the parallel gate"]
fn expanded_read_step_uses_contextual_range_separation() {
    let c_source = r#"
        struct owned_string {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 owned_string_pop(struct owned_string* owner) {
            int32 index;
            int32 value;
            index = owner->len - 1;
            value = owner->data[index];
            owner->data[index] = 0;
            owner->len = index;
            return value;
        }
    "#;
    let click_source = r#"
        predicate terminated_at(data: int32[], length: int32) {
            data[length] == 0
        }

        resource owned_string(owner: struct owned_string*) {
            owns owner->len;
            owns owner->cap;
            owns owner->data;
            owns owner->data[0..owner->cap];
            fact 0 <= owner->len;
            fact owner->len < owner->cap;
            fact terminated_at(owner->data, owner->len);
            fact separate(
                memory(*owner),
                memory(owner->data[0..owner->cap])
            );
        }

        verifying "owned_string_pop.c";

        int32 owned_string_pop(struct owned_string* owner) {
            requires 1 <= owner->len;
            owns owned_string(owner);
            ensures result == old(owner->data[owner->len - 1]);
            ensures owner->len == old(owner->len) - 1;
            ensures owner->cap == old(owner->cap);
            ensures owner->data == old(owner->data);
            ensures owner->data[owner->len] == 0;
        } by {
            unfold(owned_string(owner));
            have 0 <= owner->len - 1 by close();
            have owner->len - 1 < owner->len by close();
            step_until(function.exit);
            have terminated_at(owner->data, owner->len) by {
                unfold(terminated_at(owner->data, owner->len));
                close();
            }
            have 0 <= owner->len by close();
            have owner->len < owner->cap by close();
            have separate(
                memory(*owner),
                memory(owner->data[0..owner->cap])
            ) by {
                close();
            }
            fold(owned_string(owner));
            close();
        }
    "#;
    let execute_offset = click_source
        .find("step_until(function.exit)")
        .expect("proof should contain execute_rest");
    let line = click_source[..execute_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = execute_offset
        - click_source[..execute_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let (expanded, _events) = crate::instrumentation::collect(|| {
        expand_c_tactic_source_at(
            click_source,
            &[("owned_string_pop.c", c_source)],
            line,
            column,
        )
    });
    let expanded = expanded.expect("the read step's generated surface certificate should check");

    // Whether the certificate defers a smart tactic is read from the checked
    // runs' events, not inferred from a tight smart-tactic clock: the
    // expanded proof runs exactly the original's smart tactics less the
    // expanded `step_until(function.exit)`.
    let smart_tactics = |source: &str| {
        let (verified, events) = crate::instrumentation::collect(|| {
            verify_c_sources(source, &[("owned_string_pop.c", c_source)])
        });
        verified.expect("the read proof should verify as a complete proof");
        events
            .iter()
            .filter_map(|event| match event {
                crate::instrumentation::VerificationEvent::TacticStarted(tactic)
                    if tactic.class == "smart" =>
                {
                    Some(tactic.tactic_name.clone())
                }
                _ => None,
            })
            .collect::<Vec<_>>()
    };
    let mut remaining = smart_tactics(click_source);
    assert!(
        remaining.iter().any(|name| name == "step_until"),
        "the original proof runs its smart `step_until`: {remaining:?}"
    );
    remaining.retain(|name| name != "step_until");
    assert_eq!(
        smart_tactics(&expanded),
        remaining,
        "the expanded certificate should contain no deferred smart tactic"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_11")]
fn decrement_contract_checks_nonnegative_and_equality_certificates() {
    let c_source = r#"
        int32 decrement(int32 value, int32 count) {
            return value - 1;
        }
    "#;
    let click_source = r#"
        verifying "decrement.c";

        int32 decrement(int32 value, int32 count) {
            requires 0 < value;
            requires value == count;
            ensures to_integer(result) == to_integer(value - 1);
        } by {
            have 0 <= to_integer(value - 1) by close();
            have to_integer(value - 1) < to_integer(value) by close();
            have to_integer(value - 1) == to_integer(count - 1) by close();
            step_until(function.exit);
            close();
        }
    "#;

    verify_c_sources(click_source, &[("decrement.c", c_source)])
        .expect("decrement arithmetic should search and check consistently");
}

/// A source tactic inside a checked branch arm, including the continuation
/// that follows a `branch`, is its own source operation: the profiler must
/// time it under its source site. Untimed, its work was reported as the
/// function's shared verifier work, which made a smart `solve` look like
/// kernel core cost.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_11")]
fn branch_continuation_tactics_are_timed_as_source_operations() {
    let c_source = r#"
        int32 pick(int32 a) {
            int32 x;
            if (a == 0) {
                return 0;
            }
            x = a;
            return x;
        }
    "#;
    let click_source = r#"
        verifying "pick.c";

        int32 pick(int32 a) {
            requires 0 <= a;
            requires a <= 10;
            ensures result == a;
        } by {
            step();
            branch {
                true => {
                    step_until(function.exit);
                    close();
                }
                false => {}
            }
            step();
            have x == a by {
                close();
            }
            step_until(function.exit);
            close();
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_c_sources(click_source, &[("pick.c", c_source)]));
    verified.expect("the branch-continuation proof should verify");
    let timed = events
        .iter()
        .filter_map(|event| match event {
            crate::instrumentation::VerificationEvent::TacticFinished { tactic, .. }
                if tactic.claim == "pick.contract" =>
            {
                Some((tactic.tactic_name.as_str(), tactic.source_index))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        timed.contains(&("step", 4)) && timed.contains(&("have", 5)),
        "the continuation's `step` and `have` must be timed at their source sites: {timed:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_12")]
fn implicit_contract_closer_is_not_a_profile_source_site() {
    let c_source = "int32 value(void) { return 7; }";
    let click_source = r#"
        verifying "value.c";
        int32 value() { ensures result == 7; } by { step_until(function.exit); }
    "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c_sources(click_source, &[("value.c", c_source)])
    });
    verified.expect("the implicit contract closer must still verify");
    let timed = events
        .iter()
        .filter_map(|event| match event {
            crate::instrumentation::VerificationEvent::TacticFinished { tactic, .. } => {
                Some(tactic)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        timed
            .iter()
            .any(|tactic| tactic.tactic_name == "step_until")
    );
    assert!(
        timed.iter().all(|tactic| tactic.source_index != usize::MAX),
        "generated closers cannot be selected in the written source: {timed:?}"
    );
}

/// The implicit tail runs a symbolic `switch` on the checked `Proof` itself: the
/// statement's arms are path cases, split on the condition that tells them
/// apart.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_12")]
fn execute_splits_a_symbolic_switch_on_the_proof() {
    let c_source = r#"
        int32 switch_break(int32 kind) {
            int32 result = 0;
            switch (kind) {
                case 0:
                    result = 10;
                    break;
                case 1:
                    result = 20;
                    break;
                default:
                    result = 30;
                    break;
            }
            return result;
        }
    "#;
    let click_source = r#"
        verifying "switch_break.c";

        int32 switch_break(int32 kind) {
            ensures result == 10 or result == 20 or result == 30;
        }
    "#;
    // The whole verification runs on one thread, so the counter it reads is
    // that thread's own; the stack is sized for an unoptimized build.
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            verify_c_sources(click_source, &[("switch_break.c", c_source)])
                .unwrap_or_else(|error| panic!("{}", error.message()));
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A short-circuit condition is false along two checked paths, so a C
/// `branch` cannot split it directly. The implicit tail first splits the checked
/// `Proof` on the condition that tells those paths apart.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_12")]
fn execute_splits_a_short_circuit_condition_on_the_proof() {
    let c_source = r#"
        int32 both_positive(int32 a, int32 b) {
            if (a > 0 && b > 0) {
                return 1;
            }
            return 0;
        }
    "#;
    let click_source = r#"
        verifying "both_positive.c";

        int32 both_positive(int32 a, int32 b) {
            ensures result == 0 or result == 1;
        }
    "#;
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            verify_c_sources(click_source, &[("both_positive.c", c_source)])
                .unwrap_or_else(|error| panic!("{}", error.message()));
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A null check on a fresh `malloc` result is an ordinary C branch: the
/// condition's two paths decide the pending allocation, one per arm, and
/// the implicit tail splits it on the checked `Proof`.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_12")]
fn execute_branches_on_a_pending_allocation_on_the_proof() {
    let c_source = r#"
        void *malloc(unsigned long size);
        void free(void *ptr);

        int f(void) {
            int *p = malloc(sizeof(int));
            if (p == 0) {
                return 0;
            }
            *p = 1;
            free(p);
            return 0;
        }
    "#;
    let click_source = r#"
        verifying "pending.c";

        int f() {
            ensures result == 0;
        }
    "#;
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            verify_c_sources(click_source, &[("pending.c", c_source)])
                .unwrap_or_else(|error| panic!("{}", error.message()));
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A loop the proof context decides at every iteration runs as ordinary
/// checked statement steps on the `Proof`. The bound is symbolic and fixed
/// by a `requires`: the
/// loop head reads the whole proof context, as every other step does.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_13")]
fn execute_walks_a_decided_loop_on_the_proof() {
    let c_source = r#"
        int32 count_to(int32 n) {
            int32 i = 0;
            while (i < n) {
                i++;
            }
            return i;
        }
    "#;
    let click_source = r#"
        verifying "count.c";

        int32 count_to(int32 n) {
            requires n == 3;
            ensures result == 3;
        }
    "#;
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            verify_c_sources(click_source, &[("count.c", c_source)])
                .unwrap_or_else(|error| panic!("{}", error.message()));
        })
        .unwrap()
        .join()
        .unwrap();
}

/// The implicit tail walks a decided loop one checked step at a time on the
/// `Proof`, so a loop that never exits must exhaust a fixed step budget and
/// name the statement it stands at, rather than run until the work limit.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn execute_stops_a_loop_that_never_exits_at_its_step_budget() {
    let c_source = r#"
        int32 spin() {
            int32 i = 0;
            while (1) {
                i = 0;
            }
            return i;
        }
    "#;
    let click_source = r#"
        verifying "spin.c";

        int32 spin() {
            ensures result == 0;
        }
    "#;
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            let error = verify_c_sources(click_source, &[("spin.c", c_source)])
                .expect_err("a loop that never exits has no function exit to reach");
            assert!(
                error
                    .message()
                    .contains("execution exhausted its 10000-step budget at region("),
                "expected the step budget refusal, got: {}",
                error.message()
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

/// `step_until` shares the implicit tail's search and its step budget, so a
/// loop that never exits before the target is refused at that budget.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn execute_until_stops_a_loop_that_never_exits_at_its_step_budget() {
    let c_source = r#"
        int32 spin_then() {
            int32 i = 0;
            while (1) {
                i = 0;
            }
            i = 1;
            return i;
        }
    "#;
    let click_source = r#"
        verifying "spin_then.c";

        int32 spin_then() {
            ensures result == 1;
        } by {
            step_until(region(3).entry);
            step_until(function.exit);
            close();
        }
    "#;
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            let error = verify_c_sources(click_source, &[("spin_then.c", c_source)])
                .expect_err("the loop never reaches the target statement");
            assert!(
                error
                    .message()
                    .contains("execution exhausted its 10000-step budget at region("),
                "expected the step budget refusal, got: {}",
                error.message()
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_13")]
fn execute_short_circuit_complements_expand_with_exact_operand_selectors() {
    for condition in ["!(a > 0 && b > 0)", "a > 0 || b > 0"] {
        let c_source = format!(
            "int32 choose(int32 a, int32 b) {{ if ({condition}) {{ return 1; }} return 2; }}"
        );
        let click_source = r#"verifying "choose.c";
int32 choose(int32 a, int32 b) {
    ensures result == 1 or result == 2;
}
"#;
        let sources = [("choose.c", c_source.as_str())];
        verify_c_sources(click_source, &sources).unwrap();
        let position =
            expansion::position_at_offset(click_source, click_source.find("ensures").unwrap());
        let expanded =
            expand_c_tactic_source_at(click_source, &sources, position.line, position.column)
                .unwrap();
        verify_c_sources(&expanded, &sources)
            .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
    }
}

fn struct_pointer_field_constructor_fixture() -> (&'static str, &'static str) {
    let c_source = r#"
        struct child { int32 value; };
        struct other { int32 value; };
        struct parent { struct child* kid; struct other* wrong; int32 scalar; };
        void unchanged(struct parent* p, struct child* kid) {}
    "#;
    // The constructor also needs nominal evidence for the stored value.
    // Relate it to a typed input so this checks the field's declared type.
    let source = r#"
        spec enum Link { Linked(struct child*), }
        verifying "field.c";
        void unchanged(struct parent* p, struct child* kid) {
            views p->kid;
            requires p->kid == kid;
            ensures Link::Linked(old(p->kid)) == Link::Linked(p->kid)
                and Link::Linked(p->kid) == Link::Linked(kid);
        }
    "#;
    (source, c_source)
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_13")]
fn algebraic_constructor_keeps_struct_pointer_field_identity_across_old() {
    let (source, c_source) = struct_pointer_field_constructor_fixture();
    verify_c_sources(source, &[("field.c", c_source)])
        .expect("a historical field retains its declared struct pointer type");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_13")]
fn algebraic_constructor_rejects_wrong_struct_and_scalar_fields() {
    let (source, c_source) = struct_pointer_field_constructor_fixture();
    for wrong in ["p->wrong", "p->scalar"] {
        let invalid = source
            .replace("Linked(old(p->kid))", &format!("Linked(old({wrong}))"))
            .replace("Linked(p->kid)", &format!("Linked({wrong})"));
        let error = verify_c_sources(&invalid, &[("field.c", c_source)])
            .expect_err("a different struct or scalar cannot fill a child pointer field");
        assert!(error.message().contains("expects struct child*"), "{error}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: false-postcondition proof took 0.579s in parallel"]
fn algebraic_constructor_field_metadata_cannot_prove_a_false_postcondition() {
    let (source, c_source) = struct_pointer_field_constructor_fixture();
    verify_c_sources(
        &source.replace(" == Link::Linked", " != Link::Linked"),
        &[("field.c", c_source)],
    )
    .expect_err("retaining a field type must not establish a false postcondition");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_14")]
fn solve_keeps_valid_integer_offset_function_goals() {
    let source = r#"
        function plus(value: Integer) -> Integer { value + 1 }
        verifying "offset.c";
        void good(uint32 input) {
            ensures plus(to_integer(input)) == to_integer(input) + 1;
            ensures to_integer(input) == to_integer(input) + 0;
        }
    "#;
    verify_c_sources(source, &[("offset.c", "void good(uint32 input) {}")])
        .expect("valid function equations and zero offsets remain provable");
}

/// One read, one name: a read through a loop alias of a field a call left
/// unchanged reads the call's unchanged-bytes source, whose cell holds the
/// field's read at the loop head. That read names it; it is not named again
/// at the projected state (`docs/internals/raise-lower-principle.md`).
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by execution_batch_14")]
fn a_read_retained_across_a_call_through_a_loop_alias_keeps_its_name() {
    let mdtest = crate::cli::parse_mdtest(
        std::path::Path::new("a_retained_pointer_field_fact_transports_through_a_loop_alias.md"),
        include_str!(
            "../../../mdtests/a_retained_pointer_field_fact_transports_through_a_loop_alias.md"
        ),
    )
    .unwrap();
    let click = mdtest.click_source.as_deref().unwrap();
    let sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let duplicates = crate::kernel::duplicate_read_names::capture(|| {
        verify_c_sources(click, &sources).unwrap();
    });
    assert!(duplicates.is_empty(), "{duplicates:?}");
}

/// One cell, one kind of name, over the whole mdtest corpus: every C mdtest
/// is verified under [`crate::kernel::mixed_read_names::capture`], which
/// lists each integer read the equality graph saw named both by a selected
/// program point and by its memory, with the line that built the
/// memory-named one. It prints the list and its count rather than failing:
/// the program-point migration (`roadmap/smart-tactics.md`) is to drive it to
/// zero. Nightly: it verifies the corpus once more, serially.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: verifies every C mdtest again under the mixed-read-name audit"]
fn every_mdtest_reports_its_mixed_read_names() {
    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests");
    let only = std::env::var("CLICK_MIXED_READ_NAMES_ONLY").ok();
    let mut paths = std::fs::read_dir(&directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "md"))
        .filter(|path| {
            only.as_deref().is_none_or(|only| {
                path.file_stem()
                    .is_some_and(|stem| stem.to_string_lossy() == only)
            })
        })
        .collect::<Vec<_>>();
    paths.sort();
    let mut total = 0;
    let mut by_origin = std::collections::BTreeMap::<String, usize>::new();
    for path in paths {
        let name = path.file_stem().unwrap().to_string_lossy().into_owned();
        let Ok(mdtest) = crate::cli::read_mdtest(&path) else {
            continue;
        };
        let (Some(click), Ok(inputs)) = (
            mdtest.click_source.as_deref(),
            crate::cli::prepare_mdtest_inputs(&mdtest),
        ) else {
            continue;
        };
        let crate::cli::VerificationInput::Bundle(sources) = &inputs else {
            continue;
        };
        let sources = sources
            .iter()
            .map(|(file, source)| (file.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let project = crate::cli::read_mdtest_project_if_needed(&path, click, &inputs)
            .ok()
            .flatten();
        // Each fixture on a thread of its own with the harness's stack, as
        // the mdtest harness runs it; the census is per thread.
        let reports = std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(64 * 1024 * 1024)
                .spawn_scoped(scope, || {
                    crate::kernel::mixed_read_names::capture(|| {
                        let _ = match &project {
                            Some(project) => {
                                crate::surface::verify_c_project(project, &sources).map(|_| ())
                            }
                            None => verify_c_sources(click, &sources).map(|_| ()),
                        };
                    })
                })
                .expect("a verifier thread")
                .join()
                .unwrap_or_default()
        });
        for report in &reports {
            let origin = report.rsplit("built at ").next().unwrap_or("").to_string();
            *by_origin.entry(origin).or_default() += 1;
            eprintln!("{name}: {report}");
        }
        total += reports.len();
    }
    eprintln!("mixed read names: {total}; by the line that built the memory-named read:");
    for (origin, count) in &by_origin {
        eprintln!("  {count:6} {origin}");
    }
}

/// One read, one name, over the whole mdtest corpus: every C mdtest is
/// verified under [`crate::kernel::duplicate_read_names::capture`], and no
/// read may be named twice for a version the assumption-free load equality
/// proves the same. Nightly: it verifies the corpus once more, serially.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: verifies every C mdtest again under the read-name audit"]
fn every_mdtest_names_each_read_once() {
    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests");
    let mut paths = std::fs::read_dir(&directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "md"))
        .collect::<Vec<_>>();
    paths.sort();
    let mut duplicates = Vec::new();
    for path in paths {
        let name = path.file_stem().unwrap().to_string_lossy().into_owned();
        let Ok(mdtest) = crate::cli::read_mdtest(&path) else {
            continue;
        };
        let (Some(click), Ok(inputs)) = (
            mdtest.click_source.as_deref(),
            crate::cli::prepare_mdtest_inputs(&mdtest),
        ) else {
            continue;
        };
        let crate::cli::VerificationInput::Bundle(sources) = &inputs else {
            continue;
        };
        let sources = sources
            .iter()
            .map(|(file, source)| (file.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let project = crate::cli::read_mdtest_project_if_needed(&path, click, &inputs)
            .ok()
            .flatten();
        let reports = crate::kernel::duplicate_read_names::capture(|| {
            let _ = match &project {
                Some(project) => crate::surface::verify_c_project(project, &sources).map(|_| ()),
                None => verify_c_sources(click, &sources).map(|_| ()),
            };
        });
        if reports.is_empty() {
            continue;
        }
        duplicates.push(format!("{name}: {reports:?}"));
    }
    assert!(duplicates.is_empty(), "{duplicates:#?}");
}

/// Where load variables still reach facts: every C mdtest is verified under
/// [`crate::kernel::load_variable_fact_census::capture`], and the facts that
/// entered a context holding a load variable are printed by kind, with the
/// mdtests that produced the most. A report, not a check: run it by name to
/// see what removing load variables from facts still has to change.
#[test]
#[ignore = "report: verifies every C mdtest under the load-variable fact census"]
fn report_load_variables_in_facts() {
    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests");
    let mut paths = std::fs::read_dir(&directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "md"))
        .collect::<Vec<_>>();
    paths.sort();
    let mut totals = std::collections::BTreeMap::<String, (usize, usize, String)>::new();
    let mut verified = 0;
    for path in paths {
        let Ok(mdtest) = crate::cli::read_mdtest(&path) else {
            continue;
        };
        let (Some(click), Ok(inputs)) = (
            mdtest.click_source.as_deref(),
            crate::cli::prepare_mdtest_inputs(&mdtest),
        ) else {
            continue;
        };
        let crate::cli::VerificationInput::Bundle(sources) = &inputs else {
            continue;
        };
        let sources = sources
            .iter()
            .map(|(file, source)| (file.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let project = crate::cli::read_mdtest_project_if_needed(&path, click, &inputs)
            .ok()
            .flatten();
        let counts = crate::kernel::load_variable_fact_census::capture(|| {
            let _ = match &project {
                Some(project) => crate::surface::verify_c_project(project, &sources).map(|_| ()),
                None => verify_c_sources(click, &sources).map(|_| ()),
            };
        });
        verified += 1;
        for (kind, (count, example)) in counts {
            let total = totals.entry(kind).or_insert((0, 0, example));
            total.0 += count;
            total.1 += 1;
        }
    }
    eprintln!("LOAD-VARIABLE FACTS over {verified} C mdtests:");
    for (kind, (count, files, example)) in &totals {
        eprintln!("  {count:>8} facts in {files:>5} mdtests  {kind}\n           e.g. {example}");
    }
}

#[cfg(feature = "fast-gate")]
test_batches! {
    file: "execution_tests.rs",
    marker: "execution_batch_",
    execution_batch_00: [
        generic_function_keeps_the_declared_struct_pointer_result_type,
        generic_result_type_does_not_unify_distinct_structs,
        generic_result_type_cannot_prove_a_false_postcondition,
        authority_establishes_and_retires_empty_stack_population,
    ],
    execution_batch_01: [
        authority_conserves_one_local_member,
        authority_cannot_reestablish_after_retirement,
        authority_rejects_automatic_storage_end_with_live_authority,
        authority_imported_pointer_without_live_storage_cannot_establish_population,
    ],
    execution_batch_02: [
        authority_cannot_create_untracked_member_before_establishment,
        authority_rejects_double_member_consumption,
        authority_cannot_retire_with_live_member,
        authority_count_requires_owned_authority,
    ],
    execution_batch_03: [
        authority_count_of_a_population_without_authority_is_refused,
        authority_plain_c_helper_call_follows_the_ordinary_call_rules,
        authority_calls_a_verified_helper_without_population_effects,
        authority_helper_returns_the_same_authority_and_member,
    ],
    execution_batch_04: [
        authority_helper_consumes_one_member_and_returns_authority,
        authority_helper_produces_one_member_and_returns_authority,
        authority_helper_cannot_claim_creation_without_folding_member,
        authority_helper_cannot_birth_imported_member_twice,
    ],
    execution_batch_05: [
        authority_creating_helper_requires_caller_authority,
        authority_helper_cannot_create_private_memory_from_opaque_authority,
        authority_helper_cannot_claim_consumption_without_spending_member,
        authority_helper_cannot_spend_imported_member_twice,
    ],
    execution_batch_06: [
        authority_consuming_helper_requires_caller_member,
        verifies_loadable_segment_proposition_for_indexed_read,
        bounded_assignment_preserves_successor_definedness,
        uninitialized_scalar_read_fails_verification,
    ],
    execution_batch_07: [
        uninitialized_local_array_read_fails_verification,
        pointer_argument_keeps_its_null_execution_path,
        step_and_execute_step_advance_one_concrete_loop_transition,
        early_return_completes_without_a_body_rerun,
    ],
    execution_batch_08: [
        symbolic_loop_bound_invariant_completes_without_a_body_rerun,
        malloc_null_check_completes_without_a_body_rerun,
        post_execution_case_split_completes_without_a_body_rerun,
        have_after_loop_completes_without_a_body_rerun,
    ],
    execution_batch_09: [
        applied_user_theorem_completes_without_a_body_rerun,
        verified_loop_summary_completes_without_a_body_rerun,
        linear_execute_checks_the_branch_arm_refusal_program,
        execute_in_loop_preservation_keeps_the_function_exit_miss,
    ],
    execution_batch_10: [
        bounded_execute_resumes_and_explores_symbolic_branches,
        verifies_fill3_c_source_with_sidecar_specification,
        bounded_solve_loop_expands_without_a_detached_summary,
        signature_mismatch_reports_direct_error,
    ],
    execution_batch_11: [
        pointer_constness_signature_mismatch_displays_both_qualifiers,
        struct_name_signature_mismatch_reports_direct_error,
        decrement_contract_checks_nonnegative_and_equality_certificates,
        branch_continuation_tactics_are_timed_as_source_operations,
    ],
    execution_batch_12: [
        implicit_contract_closer_is_not_a_profile_source_site,
        execute_splits_a_symbolic_switch_on_the_proof,
        execute_splits_a_short_circuit_condition_on_the_proof,
        execute_branches_on_a_pending_allocation_on_the_proof,
    ],
    execution_batch_13: [
        execute_walks_a_decided_loop_on_the_proof,
        execute_short_circuit_complements_expand_with_exact_operand_selectors,
        algebraic_constructor_keeps_struct_pointer_field_identity_across_old,
        algebraic_constructor_rejects_wrong_struct_and_scalar_fields,
    ],
    execution_batch_14: [
        solve_keeps_valid_integer_offset_function_goals,
        a_read_retained_across_a_call_through_a_loop_alias_keeps_its_name,
    ],
}

/// Two paths reaching equal states are named separately: each recorded name
/// is found by its own path's point, whatever the memories hold.
#[test]
fn recorded_points_are_named_by_the_point_each_path_reached() {
    let start = ExecutionState::new().with_memory(crate::kernel::SymbolicMemory::new());
    let left = start
        .clone()
        .with_memory(crate::kernel::SymbolicMemory::new());
    let right = start.with_memory(crate::kernel::SymbolicMemory::new());
    assert_eq!(left, right);
    let mut states = RecordedStates::default();
    states.insert(ProgramPointSelector::Mark("left".into()), left.clone());
    states.insert(ProgramPointSelector::Mark("right".into()), right.clone());
    let name = |state: &ExecutionState| states.point_name(state.program_point_id().unwrap());
    assert_eq!(
        name(&left),
        Some(&ProgramPointSelector::Mark("left".into()))
    );
    assert_eq!(
        name(&right),
        Some(&ProgramPointSelector::Mark("right".into()))
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.58s in the parallel gate; source-point separation stays in the fast layout test"]
fn a_loop_test_does_not_publish_the_whole_loops_exit_state() {
    let c_source = r#"
        int32 count_two() {
            int32 i;
            i = 0;
            while (i < 2) { i = i + 1; }
            return i;
        }
    "#;
    let source = r#"
        verifying "count_two.c";
        int32 count_two() {
            ensures result == 2 by {
                step(); step(); step();
                have at(statement(2).exit, i) == 0 by close();
            }
        }
    "#;
    assert!(
        verify_c_sources(source, &[("count_two.c", c_source)]).is_err(),
        "a successful head test must not establish the later whole-loop exit"
    );
}
