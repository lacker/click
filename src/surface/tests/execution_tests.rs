use super::*;
use crate::kernel::CLoopEffectOrigin;

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
            execute();
            simp();
        }
    "#;
    parser::parse_file_items(click_source)
        .expect("the source fold/unfold fixture must parse independently of mode gating");
    verify_c0_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect("the creator may establish and retire one empty population");
}

#[test]
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
            have count(reference(&x)) == 0 by { simp(); }
            fold(reference(&x));
            have count(reference(&x)) == 1 by { simp(); }
            unfold(reference(&x));
            have count(reference(&x)) == 0 by { simp(); }
            unfold(authority(reference(&x)));
            execute();
            simp();
        }
    "#;
    verify_c0_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect("one checked member changes count from zero to one and back");
}

#[test]
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
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("a retired population cannot be established a second time");
    assert!(error.message().contains("AlreadyEstablished"), "{error:?}");
}

#[test]
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
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("automatic storage cannot end while its authority remains live");
    assert!(error.message().contains("authority"), "{error:?}");
}

#[test]
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
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(
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
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(
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
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(
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
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("retirement requires an empty population");
    assert!(error.message().contains("OutstandingMembers"), "{error:?}");
}

#[test]
fn authority_count_requires_owned_authority() {
    let c_source = "int32 value(int32* p) { return 7; }";
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        verifying "authority_stack.c";

        int32 value(int32* p) {
            owns p[0..1];
            ensures result == 7;
        } by {
            have count(reference(p)) == 0 by { simp(); }
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("zero is not observable without matching authority");
    assert!(error.message().contains("authority"), "{error:?}");
}

#[test]
fn authority_count_of_a_population_without_authority_is_refused() {
    let c_source = "int32 value(int32* p) { return 7; }";
    let click_source = r#"
        authorized abstract resource reference(p: int32*);
        verifying "authority_stack.c";

        int32 value(int32* p) {
            ensures count(reference(p)) == 0;
        } by {
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("a count needs the population's authority");
    assert!(error.message().contains("count"), "{error:?}");
}

#[test]
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
        } by {
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("an unverified helper without a contract cannot be called opaquely");
    // The helper's contract moves no resource, so population rules add no
    // refusal of its own; the ordinary rule for unverified callees applies.
    assert!(
        error
            .message()
            .contains("its contract has not been verified yet"),
        "{error:?}"
    );
}

#[test]
fn authority_calls_a_verified_helper_without_population_effects() {
    let c_source = r#"
        int32 helper(void) { return 7; }
        int32 value(void) { return helper(); }
    "#;
    let click_source = r#"
        verifying "authority_stack.c";

        int32 helper() {
            ensures result == 7;
        } by {
            execute();
            simp();
        }

        int32 value() {
            ensures result == 7;
        } by {
            execute();
            simp();
        }
    "#;
    verify_c0_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect("an independently verified helper preserves an untouched population ledger");
}

#[test]
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
        } by {
            execute();
            simp();
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
            execute();
            simp();
        }
    "#;
    verify_c0_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect("a verified helper returns the exact authority and member it received");
}

#[test]
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
            execute();
            simp();
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
            have count(reference(&x)) == 0 by { simp(); }
            unfold(authority(reference(&x)));
            execute();
            simp();
        }
    "#;
    verify_c0_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect("a verified helper consumes one owned member and returns authority");
}

#[test]
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
            execute();
            simp();
        }

        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(authority(reference(&x)));
            step();
            step();
            step();
            have count(reference(&x)) == 1 by { simp(); }
            unfold(reference(&x));
            unfold(authority(reference(&x)));
            execute();
            simp();
        }
    "#;
    verify_c0_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect("a verified helper creates one owned member and returns authority");
}

#[test]
fn authority_helper_cannot_claim_creation_without_folding_member() {
    let c_source = r#"int32 add_reference(int32* p) { return 7; }"#;
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        verifying "authority_stack.c";
        int32 add_reference(int32* p) {
            owns authority(reference(p));
            produces reference(p);
            ensures result == 7;
        } by {
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(
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
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("one helper proof cannot create two members");
    assert!(error.message().contains("reference"), "{error:?}");
}

#[test]
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
            execute();
            simp();
        }
        int32 value() {
            ensures result == 7;
        } by {
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("a helper cannot create a member without concrete caller authority");
    assert!(error.message().contains("authority"), "{error:?}");
}

#[test]
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
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(
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
fn authority_helper_cannot_claim_consumption_without_spending_member() {
    let c_source = r#"int32 drop_reference(int32* p) { return 7; }"#;
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        verifying "authority_stack.c";
        int32 drop_reference(int32* p) {
            owns authority(reference(p));
            consumes reference(p);
            ensures result == 7;
        } by {
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("a declared consume needs a checked member death in the helper proof");
    assert!(error.message().contains("reference"), "{error:?}");
}

#[test]
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
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("one imported member cannot be consumed twice");
    assert!(error.message().contains("reference"), "{error:?}");
}

#[test]
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
            execute();
            simp();
        }
        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(authority(reference(&x)));
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(
        &authority_stack_project(click_source),
        &[("authority_stack.c", c_source)],
    )
    .expect_err("authority alone cannot supply a member consumed by a helper");
    assert!(error.message().contains("reference"), "{error:?}");
}

#[test]
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

                ensures returns_loaded_value: result == p[index] by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("read_index.c", c_source)])
        .expect("viewable segment should prove indexed read viewability");

    assert_eq!(verified.len(), 1);
}

#[test]
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
                ensures result == (x + 1) + 1;
            } by {
                execute();
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("add_twice.c", c_source)])
        .expect("the bound on x should prove both additions defined");
}

#[test]
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
                ensures result == 0 by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("read_uninitialized.c", c_source)])
        .expect_err("an uninitialized scalar read must not verify");
    assert!(
        error.message().contains("read of uninitialized storage"),
        "{}",
        error.message()
    );
}

#[test]
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
                ensures result == 0 by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("read_uninitialized_array.c", c_source)])
        .expect_err("an uninitialized local array read must not verify");
    assert!(
        error.message().contains("read of uninitialized storage"),
        "{}",
        error.message()
    );
}

#[test]
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
                ensures result == 0 by auto;
            }
        "#;

    verify_c0_sources(click_source, &[("pointer_is_null.c", c_source)])
        .expect_err("an unconstrained pointer parameter may be null");
}

#[test]
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
                    simp();
                }
            }
        "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    let verified = verify_c0_sources(click_source, &[("count_two.c", c_source)])
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
            } by {
                execute();
                simp();
            }
        "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c0_sources(click_source, &[("clamp.c", c_source)])
        .expect("an early return should verify from its retained statement theorems");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "a path that returns before the end of the body should complete without rerunning it"
    );
}

#[test]
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
                simp();
            }
        "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c0_sources(click_source, &[("count_to_n.c", c_source)])
        .expect("a symbolic loop bound with a conjunctive invariant should verify");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "the invariant conjuncts the loop theorem assumed are retained by the loop step"
    );
}

#[test]
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
            } by {
                execute();
                simp();
            }
        "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c0_sources(click_source, &[("alloc_then_free.c", c_source)])
        .expect("a null-checked allocation that is freed should verify");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "the null check resolves the pending allocation in the reached state as it does in execution"
    );
}

#[test]
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
                execute();
                if a == 5 {
                    simp();
                } else {
                    simp();
                }
            }
        "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c0_sources(click_source, &[("clamp_positive.c", c_source)])
        .expect("a post-execution case split should verify");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "forked outcome paths carry forked traces with their case arms"
    );
}

#[test]
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
                have i == 1 by simp;
                have j == 1 by simp;
                step();
                simp();
            }
        "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c0_sources(click_source, &[("count_then_add.c", c_source)])
        .expect("facts established by `have` after the loops should verify the return");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "the return statement's theorem lists the `have` facts; the retained context vouches for them"
    );
}

#[test]
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
                    simp();
                }
            }

            int32 increment(int32 x) {
                requires x < 2147483647;
                ensures result == x + 1;
            } by {
                apply(increment_is_defined(x));
                step();
                simp();
            }
        "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c0_sources(click_source, &[("increment.c", c_source)])
        .expect("an applied user theorem should discharge the step's definedness");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "the applied theorem's fact is in the context the step was proved under"
    );
}

#[test]
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
                    simp();
                }
                loop {
                    decreases 3 - i;
                    invariant i >= 0;
                    invariant i <= 3;
                }
                step();
                simp();
            }
        "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
        .expect("verified loop summary should retain its checked statement theorem");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "a verified loop summary should complete without rerunning the function body"
    );
}

#[test]
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
                    execute();
                    simp();
                    simp();
                }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("choose_after_init.c", c_source)])
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
        assert_eq!(proof_if.then_tactics.last(), Some(&ProofTactic::Assumption));
        assert_eq!(proof_if.else_tactics.last(), Some(&ProofTactic::Assumption));
        ProofCertificate::from_proof_tactics(&expanded)
            .expect("bounded branch expansion should be a surface certificate");
    }
}

#[test]
fn verifies_fill3_c0_source_with_sidecar_specification() {
    let verified = verify_c0_sources(FILL3_CLICK, &[("fill3.c", FILL3_C)])
        .expect("fill3 sidecar should verify");

    assert_eq!(verified.len(), 1);
    let verified = &verified[0];
    let crate::kernel::CExpression::Value(crate::kernel::CValue::Pointer(argument)) =
        &verified.specification.arguments()[0]
    else {
        panic!("fill3's input is a pointer");
    };
    let Some(crate::kernel::PointerDesignation::Unresolved(input_identity)) =
        argument.designation()
    else {
        panic!("fill3 must retain an opaque native span identity");
    };
    let base = argument.pointer().clone();
    let first = base.clone();
    let second = offset_pointer_by_int32_elements(base.clone(), Bitvector32Term::Constant(1));
    let third = offset_pointer_by_int32_elements(base.clone(), Bitvector32Term::Constant(2));
    let local_i = Pointer {
        block: "local:i".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let initial_memory = memory_with_symbolic_loadable_cells(
        CMemory::new(),
        &std::collections::BTreeMap::from([(
            "p".to_string(),
            ConcreteMemoryRangeSeed {
                base: base.clone(),
                bytes: 12,
                element_width: 4,
                element_type: Some(CType::Int32),
                struct_layout: None,
            },
        )]),
    );
    let initial_resources =
        ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(3),
        )));
    let expected_requirement = CResourceSpec::memory(
        CMemorySegment::new(
            CExpression::Variable("p".into()),
            CExpression::Value(int32(0)),
            CExpression::Value(int32(3)),
        ),
        CResourceAccessMode::Own,
        CResourceTransferRole::Consume,
        CResourceSnapshot::Entry,
    )
    .with_native_span_requirements(vec![crate::kernel::CNativeSpanRequirement {
        access_policy: crate::kernel::CTypedAccessPolicy::CAllocatedAccessAllowed,
        carrier: CExpression::Variable("p".into()),
        element_type: CType::Int32,
        count: CExpression::Value(int32(3)),
    }]);
    let expected_entry_contract = c_function(
        CType::Int32,
        "fill3",
        vec![crate::kernel::c_parameter("p", CType::Int32Pointer)],
        crate::kernel::c_return(CExpression::Value(int32(2))),
    )
    .with_resource_summary(vec![expected_requirement.clone()], Vec::new());
    let initial_memory = crate::kernel::c_state_with_assumed_native_record_inputs(
        &CState::new()
            .with_memory(initial_memory)
            .with_resource_context(initial_resources.clone()),
        &expected_entry_contract,
        verified.specification.arguments(),
        &[],
        &crate::kernel::PureFactContext::new(),
    )
    .expect("the independent fill3 contract admits its typed input span")
    .memory()
    .clone();
    let final_memory = initial_memory
        .clone()
        .with_block("local:i", 4)
        .store(first, int32(0))
        .store(second, int32(1))
        .store(third, int32(2))
        .store(local_i, int32(3))
        .without_local_block(&"local:i".into());

    // The entry has a creation ledger with a fresh
    // identity; it records nothing here.
    assert!(
        verified
            .specification
            .state()
            .equal_up_to_unused_creation_ledgers(
                &CState::new()
                    .with_population_creation_tracking()
                    .with_memory(initial_memory)
                    .with_resource_context(initial_resources.clone())
            )
    );
    assert_eq!(
        verified.specification.arguments(),
        &[CExpression::Value(CValue::Pointer(
            crate::kernel::CPointerValue::new(base.clone(), CType::Int32Pointer).with_designation(
                crate::kernel::PointerDesignation::Unresolved(*input_identity)
            ),
        ))]
    );
    assert!(
        verified
            .specification
            .outcome()
            .equal_up_to_unused_creation_ledgers(&CFunctionOutcome::Return {
                value: int32(2),
                state: Box::new(
                    CState::new()
                        .with_population_creation_tracking()
                        .with_memory(final_memory)
                        .with_resource_context(initial_resources)
                ),
            })
    );
    assert_eq!(
        implication_body(verified.theorem.proposition()),
        &Proposition::CFunctionPartiallySatisfiesSpecification {
            function: Box::new(
                {
                    let parsed = syntax::parse_function(FILL3_C)
                        .expect("fill3 should parse")
                        .to_kernel_function();
                    let CStatement::Seq(prefix, suffix) = parsed.body().clone() else {
                        panic!("fill3 body should have a prefix and suffix");
                    };
                    let CStatement::Seq(loop_statement, result) = suffix.as_ref().clone() else {
                        panic!("fill3 suffix should contain the loop and return");
                    };
                    let CStatement::While {
                        condition,
                        invariant,
                        invariant_checks,
                        body,
                        ..
                    } = loop_statement.as_ref().clone()
                    else {
                        panic!("fill3 suffix should start with a loop");
                    };
                    c_function(
                        CType::Int32,
                        "fill3",
                        vec![crate::kernel::c_parameter("p", CType::Int32Pointer)],
                        c_seq(
                            prefix.as_ref().clone(),
                            c_seq(
                                c_while_with_invariant_and_effect_checks(
                                    condition,
                                    invariant,
                                    invariant_checks,
                                    vec![
                                        // A resource-derived frame is lowered without
                                        // segments; the kernel installs its ranges from
                                        // the checked entry transition.
                                        CLoopEffectCheck::new_with_origin(
                                            CLoopEffect::Mutable(Vec::new()),
                                            CLoopEffectSpan::Whole,
                                            CLoopEffectOrigin::InheritedResourceDerived,
                                            Some(
                                                "loop 0 inherited owned resource frame".to_string(),
                                            ),
                                        )
                                        .with_validated_ranges(vec![CMemoryRange::new(
                                            base.clone(),
                                            Bitvector32Term::Constant(0),
                                            Bitvector32Term::Constant(3),
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
                .with_resource_summary(vec![expected_requirement], Vec::new(),)
                .with_contract(
                    vec![SpecProposition::MemoryLoadable {
                        memory: SpecMemory::Current,
                        base: SpecExpression::CExpression(CExpression::Variable("p".to_string(),)),
                        start: SpecExpression::Value(int32(0)),
                        end: SpecExpression::Value(int32(3)),
                        element_width: 4,
                    }],
                    vec![SpecProposition::Comparison {
                        left: SpecExpression::CExpression(CExpression::Variable(
                            crate::kernel::C_CONTRACT_RESULT_NAME.to_string(),
                        )),
                        operator: CComparisonOperator::Equal,
                        right: SpecExpression::Value(int32(2)),
                    }],
                    // The write footprint is not lowered: the kernel projects it
                    // from the resource clause, so the explicit list stays empty.
                    Vec::new(),
                    vec![CFunctionContractClaim::ensure_proposition(0, 0)],
                    true,
                )
                .with_resource_derived_mutable_frame()
            ),
            specification: Box::new(verified.specification.clone()),
        }
    );
}

#[test]
fn bounded_auto_loop_expands_without_a_detached_summary() {
    let sources = [("fill3.c", FILL3_C)];
    let position = c0_tactic_source_position(FILL3_CLICK, &sources, "fill3.returns_second", 0)
        .expect("the default auto proof should have a source position");
    let expanded =
        expand_c0_tactic_source_at(FILL3_CLICK, &sources, position.line, position.column)
            .expect("bounded loop execution should have a surface certificate");

    assert!(!expanded.contains("summarize("), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the bounded loop certificate should freshly check");
}

#[test]
fn signature_mismatch_reports_direct_error() {
    let source = FILL3_CLICK.replace("int32* p", "int32 q");
    let error = verify_c0_sources(&source, &[("fill3.c", FILL3_C)])
        .expect_err("wrong signature should fail");

    assert!(
        error.message().contains("signature mismatch"),
        "{}",
        error.message()
    );
}

#[test]
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
            let error = verify_c0_sources(&click_source, &[("read.c", &c_source)])
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
            verify_c0_sources(&click_source, &[("read.c", &c_source)])
                .expect("matching pointee qualifiers must still verify");
        }
    }
}

#[test]
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
            ensures result == old(p->value) by auto;
        }
    "#;

    let error = verify_c0_sources(click_source, &[("get_value.c", c_source)])
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
            execute();
            simp();
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
            execute();
            have 0 <= owner->pos by simp;
            have owner->pos <= owner->len by simp;
            have separate(
                memory(*owner),
                memory(owner->data[0..owner->len])
            ) by {
                simp();
            }
            fold(input_cursor(owner));
            simp();
        }

    "#;

    let sources = [
        ("input_cursor_peek.c", c_source),
        ("input_cursor_take.c", take_c_source),
    ];
    let final_simp = click_source
        .rfind("simp();")
        .expect("final simp should exist");
    let position = expansion::position_at_offset(click_source, final_simp);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("the grouped simp should emit a non-circular surface certificate");
    verify_c0_sources(&expanded, &sources)
        .expect("the grouped simp surface certificate should check from fresh source");
}

#[test]
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
            unfold(terminated_at);
            step();
            have terminated_at(owner->data, owner->len) by {
                unfold(terminated_at);
                simp();
            }
            have owner->data[owner->len] == 0 by simp;
            have 0 <= owner->len by simp;
            have owner->len < owner->cap by simp;
            have separate(
                memory(*owner),
                memory(owner->data[0..owner->cap])
            ) by {
                simp();
            }
            fold(owned_string(owner));
            step();
            simp();
        }
    "#;

    let (verified, _events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("owned_string_set.c", c_source)])
    });
    verified.expect("explicit store certificate should verify");

    let smart_step = click_source
        .rfind("step();")
        .expect("the resource-backed return step should be present");
    let position = expansion::position_at_offset(click_source, smart_step);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("owned_string_set.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained Have and statement step should expand");
    assert!(expanded.contains("have "), "{expanded}");
    assert!(expanded.contains("step();"), "{expanded}");
    verify_c0_sources(&expanded, &[("owned_string_set.c", c_source)])
        .expect("the rewritten resource-backed step should verify normally");
}

#[test]
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
            have 0 <= owner->len - 1 by simp;
            have owner->len - 1 < owner->len by simp;
            execute();
            have terminated_at(owner->data, owner->len) by {
                unfold(terminated_at);
                simp();
            }
            have 0 <= owner->len by simp;
            have owner->len < owner->cap by simp;
            have separate(
                memory(*owner),
                memory(owner->data[0..owner->cap])
            ) by {
                simp();
            }
            fold(owned_string(owner));
            simp();
        }
    "#;
    let execute_offset = click_source
        .find("execute()")
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
        expand_c0_tactic_source_at(
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
    // expanded `execute()`.
    let smart_tactics = |source: &str| {
        let (verified, events) = crate::instrumentation::collect(|| {
            verify_c0_sources(source, &[("owned_string_pop.c", c_source)])
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
        remaining.iter().any(|name| name == "execute"),
        "the original proof runs its smart `execute()`: {remaining:?}"
    );
    remaining.retain(|name| name != "execute");
    assert_eq!(
        smart_tactics(&expanded),
        remaining,
        "the expanded certificate should contain no deferred smart tactic"
    );
}

#[test]
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
            ensures result == value - 1;
        } by {
            have 0 <= value - 1 by simp;
            have value - 1 < value by simp;
            have value - 1 == count - 1 by simp;
            execute();
            simp();
        }
    "#;

    verify_c0_sources(click_source, &[("decrement.c", c_source)])
        .expect("decrement arithmetic should search and check consistently");
}

/// A source tactic inside a checked branch arm, including the continuation
/// that follows a `branch`, is its own source operation: the profiler must
/// time it under its source site. Untimed, its work was reported as the
/// function's shared verifier work, which made a smart `simp` look like
/// kernel core cost.
#[test]
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
            branch then {
                execute();
                simp();
            } else {}
            step();
            have x == a by {
                simp();
            }
            execute();
            simp();
        }
    "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("pick.c", c_source)])
    });
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

/// `execute()` runs a symbolic `switch` on the checked `Proof` itself: the
/// statement's arms are path cases, split on the condition that tells them
/// apart.
#[test]
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
        } by {
            execute();
            simp();
        }
    "#;
    // The whole verification runs on one thread, so the counter it reads is
    // that thread's own; the stack is sized for an unoptimized build.
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            verify_c0_sources(click_source, &[("switch_break.c", c_source)])
                .unwrap_or_else(|error| panic!("{}", error.message()));
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A short-circuit condition is false along two checked paths, so a C
/// `branch` cannot split it directly. `execute()` first splits the checked
/// `Proof` on the condition that tells those paths apart.
#[test]
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
        } by {
            execute();
            simp();
        }
    "#;
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            verify_c0_sources(click_source, &[("both_positive.c", c_source)])
                .unwrap_or_else(|error| panic!("{}", error.message()));
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A null check on a fresh `malloc` result is an ordinary C branch: the
/// condition's two paths decide the pending allocation, one per arm, and
/// `execute()` splits it on the checked `Proof`.
#[test]
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
        } by {
            execute();
            simp();
        }
    "#;
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            verify_c0_sources(click_source, &[("pending.c", c_source)])
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
        } by {
            execute();
            simp();
        }
    "#;
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            verify_c0_sources(click_source, &[("count.c", c_source)])
                .unwrap_or_else(|error| panic!("{}", error.message()));
        })
        .unwrap()
        .join()
        .unwrap();
}

/// `execute()` walks a decided loop one checked step at a time on the
/// `Proof`, so a loop that never exits must exhaust a fixed step budget and
/// name the statement it stands at, rather than run until the work limit.
#[test]
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
        } by {
            execute();
            simp();
        }
    "#;
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            let error = verify_c0_sources(click_source, &[("spin.c", c_source)])
                .expect_err("a loop that never exits has no function exit to reach");
            assert!(
                error
                    .message()
                    .contains("`execute` exhausted its 10000-step budget at statement("),
                "expected the step budget refusal, got: {}",
                error.message()
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

/// `execute_until` shares `execute()`'s search and its step budget, so a
/// loop that never exits before the target is refused at that budget.
#[test]
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
            execute_until(statement(3));
            execute();
            simp();
        }
    "#;
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            let error = verify_c0_sources(click_source, &[("spin_then.c", c_source)])
                .expect_err("the loop never reaches the target statement");
            assert!(
                error
                    .message()
                    .contains("`execute` exhausted its 10000-step budget at statement("),
                "expected the step budget refusal, got: {}",
                error.message()
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn execute_short_circuit_complements_expand_with_exact_operand_selectors() {
    for condition in ["!(a > 0 && b > 0)", "a > 0 || b > 0"] {
        let c_source = format!(
            "int32 choose(int32 a, int32 b) {{ if ({condition}) {{ return 1; }} return 2; }}"
        );
        let click_source = r#"verifying "choose.c";
int32 choose(int32 a, int32 b) {
    ensures result == 1 or result == 2;
} by { execute(); simp(); }
"#;
        let sources = [("choose.c", c_source.as_str())];
        verify_c0_sources(click_source, &sources).unwrap();
        let position =
            expansion::position_at_offset(click_source, click_source.find("execute()").unwrap());
        let expanded =
            expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
                .unwrap();
        verify_c0_sources(&expanded, &sources)
            .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
    }
}

#[test]
fn numeric_address_equation_cannot_recover_a_sibling_object_designation() {
    let c = "struct Pair { int first; int second; }; \
             int read_word(unsigned long word, struct Pair* p) { return *((int*)word); }";
    let source = r#"
        verifying "word.c";
        int32 read_word(uint64 word, struct Pair* p) {
            views p->second;
            requires word == address(&p->first + 1);
            ensures result == p->second;
        } by { execute(); simp(); }
    "#;
    let error = verify_c0_sources(source, &[("word.c", c)])
        .expect_err("numeric equality must not recover a dereferenceable sibling designation");
    assert!(error.message().contains("invalid memory access"), "{error:?}");
}
