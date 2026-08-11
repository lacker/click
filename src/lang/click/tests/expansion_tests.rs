use super::*;

#[test]
fn smart_simp_expansion_replays_as_surface_click() {
    let c_source = r#"
            int32 identity(int32 x, int32 y, int32 z) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x, int32 y, int32 z) {
                ensures result == x by { execute(); simp(); }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)])
        .expect("smart simp should verify");
    let expanded = verified[0]
        .expanded_proof_source()
        .expect("smart simp should lower to surface tactics");
    let expanded_source = click_source.replacen("by { execute(); simp(); }", &expanded, 1);
    verify_c0_sources(&expanded_source, &[("identity.c", c_source)])
        .expect("printed smart simp expansion should replay");
}

#[test]
fn selected_post_execution_simp_waits_for_its_surface_closer() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                execute();
                simp();
            }
        "#;
    let simp_offset = click_source
        .find("simp();")
        .expect("proof should contain the selected simp");
    let line = click_source[..simp_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = simp_offset
        - click_source[..simp_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("selected post-execution simp should expand after finalization");
    assert!(!expanded.contains("simp();"), "{expanded}");
    assert!(
        expanded.contains("assumption();") || expanded.contains("normalize();"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("selected post-execution simp expansion should replay");
}

#[test]
fn selected_post_execution_simp_keeps_the_surviving_execution_branch() {
    let c_source = r#"
            struct node {
                int32 value;
                struct node* next;
            };

            struct node* prepend(int32 value, struct node* tail) {
                struct node* node = malloc(sizeof(struct node));
                if (node == 0) {
                    return tail;
                }
                node->value = value;
                node->next = tail;
                return node;
            }
        "#;
    let click_source = r#"
            resource allocated_list(node: struct node*) {
                if node != 0 {
                    contains allocation(node, sizeof(struct node));
                    owns object(node);
                    contains allocated_list(node->next);
                }
            }

            verifying "prepend.c";

            struct node* prepend(int32 value, struct node* tail) {
                consumes allocated_list(tail);
                produces allocated_list(result);
                ensures result == tail or result != 0;
                ensures result != tail implies result->value == value;
                ensures result != tail implies result->next == tail;
            } by {
                execute();
                if result == tail {
                    simp();
                } else {
                    fold(allocated_list(result));
                    simp();
                }
            }
        "#;
    let selected_simp = click_source
        .rfind("simp();")
        .expect("success branch should contain a simp");
    let position = expansion::position_at_offset(click_source, selected_simp);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("prepend.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the selected success-branch simp should expand");
    verify_c0_sources(&expanded, &[("prepend.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "the selected success-branch simp expansion should replay: {}\n{expanded}",
            error.message()
        )
    });
}

#[test]
fn returning_malloc_result_expands_to_replayable_statement_steps() {
    let c_source = r#"
            int32* allocate_int32s(int32 count) {
                int32* data;
                data = malloc(count * 4);
                return data;
            }
        "#;
    let click_source = r#"
            resource maybe_allocated_int32s(data: int32*, count: int32) {
                if data != 0 {
                    contains allocation(data, count * 4);
                    owns data[0..count];
                }
            }

            verifying "allocate_int32s.c";

            int32* allocate_int32s(int32 count) {
                requires 1 <= count;
                requires count <= 536870911;
                produces maybe_allocated_int32s(result, count);
            } by {
                execute();
                fold(maybe_allocated_int32s(result, count));
                simp();
            }
        "#;
    let execute = click_source
        .find("execute();")
        .expect("proof should contain the selected execute");
    let position = expansion::position_at_offset(click_source, execute);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("allocate_int32s.c", c_source)],
        position.line,
        position.column,
    )
    .expect("malloc-return execution should expand");
    assert!(!expanded.contains("execute();"), "{expanded}");
    assert!(expanded.contains("step()"), "{expanded}");
    verify_c0_sources(&expanded, &[("allocate_int32s.c", c_source)])
        .expect("expanded malloc-return statement steps should replay");
}

#[test]
fn selected_post_execution_smart_have_uses_its_path_certificate() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                execute();
                have result == x by simp;
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have result")
        .expect("proof should contain the selected have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("selected post-execution smart have should expand after finalization");
    assert!(!expanded.contains("have result == x by simp"), "{expanded}");
    assert!(expanded.contains("have result == x by {"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("selected post-execution have certificate should replay");
}

#[test]
fn selected_post_execution_capture_ignores_nested_certificate_indices() {
    let c_source = r#"
            int32 set(int32* data, int32 value) {
                data[0] = value;
                return value;
            }
        "#;
    let click_source = r#"
            verifying "set.c";

            int32 set(int32 data[], int32 value) {
                owns data[0..1];
                mutable data[0..1];
                ensures result == value;
                ensures data[0] == value;
            } by {
                execute();
                have value == value by { normalize(); }
                have result == value by { normalize(); }
                have data[0] == value by simp;
                frame();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have data[0]")
        .expect("proof should contain the selected have");
    let position = expansion::position_at_offset(click_source, have_offset);

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("set.c", c_source)],
        position.line,
        position.column,
    )
    .expect("nested certificate replay must not leak later deferred tactics into the capture");
    assert_eq!(expanded.matches("frame();").count(), 1, "{expanded}");
    verify_c0_sources(&expanded, &[("set.c", c_source)])
        .expect("the selected post-execution have expansion should replay");
}

#[test]
fn post_execution_transport_observes_a_preceding_have() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                execute();
                have result == x by {
                    normalize();
                }
                transport(result == x, result == x) using {
                    result == x;
                }
                assumption();
            }
        "#;

    verify_c0_sources(click_source, &[("identity.c", c_source)])
        .expect("post-execution tactics should replay in source order");
}

#[test]
fn selected_post_execution_transport_emits_an_explicit_certificate() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                execute();
                have result == x by {
                    normalize();
                }
                transport(result == x, result == x);
                assumption();
            }
        "#;
    let transport_offset = click_source
        .find("transport(")
        .expect("proof should contain the selected transport");
    let line = click_source[..transport_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = transport_offset
        - click_source[..transport_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("selected post-execution transport should expand after finalization");
    assert!(expanded.contains("transport(result == x, result == x) using {"));
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("post-execution transport certificate should replay");
}

#[test]
fn selected_post_execution_smart_apply_uses_exact_path_premises() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            theorem int32_equality_symmetric(first: int32, second: int32) {
                requires first == second;
                ensures second == first by {
                    simp();
                }
            }

            verifying "identity.c";

            int32 identity(int32 x) {
                ensures x == result;
            } by {
                execute();
                apply(int32_equality_symmetric(result, x));
                simp();
            }
        "#;
    let apply_offset = click_source
        .find("apply(int32")
        .expect("proof should contain the selected apply");
    let line = click_source[..apply_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = apply_offset
        - click_source[..apply_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("selected post-execution smart apply should expand after finalization");
    assert!(!expanded.contains("apply(int32_equality_symmetric(result, x));"));
    assert!(
        expanded.contains("apply(int32_equality_symmetric(result, x)) using {"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("selected post-execution apply certificate should replay");
}

#[test]
fn smart_apply_surfaces_a_framed_comparison_after_an_immutable_call() {
    let peek_c_source = r#"
            int32 peek(int32* data) {
                return data[0];
            }
        "#;
    let pipeline_c_source = r#"
            int32 pipeline(int32* data, int32 expected) {
                int32 observed;
                observed = peek(data);
                return observed;
            }
        "#;
    let click_source = r#"
            theorem int32_equality_transitive(first: int32, second: int32, third: int32) {
                requires first == second;
                requires second == third;
                ensures first == third by {
                    simp();
                }
            }

            resource equal_cell(data: int32*, expected: int32) {
                owns data[0..1];
                fact data[0] == expected;
            }

            verifying "pipeline.c";
            verifying "peek.c";

            int32 peek(int32* data) {
                views data[0..1];
                immutable;
                ensures result == data[0] by auto;
            }

            int32 pipeline(int32* data, int32 expected) {
                views equal_cell(data, expected);
                immutable;
                ensures result == expected;
            } by {
                observe(equal_cell(data, expected));
                execute_until(statement(2));
                apply(int32_equality_transitive(observed, data[0], expected));
                execute();
                frame();
                simp();
            }
        "#;

    verify_c0_sources(
        click_source,
        &[("peek.c", peek_c_source), ("pipeline.c", pipeline_c_source)],
    )
    .expect("smart apply should surface the framed array equality after the call");
}

#[test]
fn smart_apply_preserves_statement_snapshots_in_explicit_premises() {
    let c_source = r#"
            int32 decrement(int32* p) {
                p[0] = 0;
                return p[0];
            }
        "#;
    let click_source = r#"
            theorem changed_one_to_zero(before: int32, after: int32) {
                requires before == 1;
                requires after == 0;
                ensures after == 0 by {
                    assumption();
                }
            }

            resource one_cell(p: int32*) {
                owns p[0..1];
                fact p[0] == 1;
            }

            verifying "decrement.c";

            int32 decrement(int32* p) {
                consumes one_cell(p);
                mutable p[0..1];
                produces p[0..1];
                ensures result == 0;
            } by {
                unfold(one_cell(p));
                step();
                have at(statement(0).entry, p[0]) == 1 by simp;
                have at(statement(0).exit, p[0]) == 0 by simp;
                apply(changed_one_to_zero(
                    at(statement(0).entry, p[0]),
                    at(statement(0).exit, p[0])
                ));
                execute();
                frame();
                simp();
            }
        "#;
    let apply_offset = click_source
        .find("apply(changed_one_to_zero")
        .expect("proof should contain the selected apply");
    let line = click_source[..apply_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = apply_offset
        - click_source[..apply_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("decrement.c", c_source)], line, column)
            .expect("the snapshot theorem application should expand");
    assert!(
        expanded.contains("at(statement(0).entry, p[0]) == 1;"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("decrement.c", c_source)])
        .expect("the explicit snapshot premises should replay");
}

#[test]
fn source_expansion_preserves_proof_marks() {
    let c_source = r#"
        int32 increment(int32 x) {
            x = x + 1;
            return x;
        }
    "#;
    let click_source = r#"
        verifying "increment.c";

        int32 increment(int32 x) {
            requires x < 2147483647;
            ensures result == at(before_increment, x) + 1 by {
                mark before_increment;
                execute();
                simp();
            }
        }
    "#;
    verify_c0_sources(click_source, &[("increment.c", c_source)])
        .expect("the marked proof should verify before expansion");

    let selected = click_source.rfind("simp();").unwrap();
    let position = expansion::position_at_offset(click_source, selected);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("increment.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the smart tactic after a mark should expand");
    assert!(expanded.contains("mark before_increment;"));
    assert!(!expanded.contains("simp();"));
    verify_c0_sources(&expanded, &[("increment.c", c_source)])
        .expect("the expansion should replay through the named snapshot");
}

#[test]
fn marked_constant_store_transport_retains_load_identity() {
    let touch_c = r#"
        struct cell { int32 value; int32 other; };

        void touch_other(struct cell* owner) {
            owner->other = 0;
        }
    "#;
    let pipeline_c = r#"
        struct cell { int32 value; int32 other; };

        int32 pipeline(struct cell* owner) {
            owner->value = 11;
            touch_other(owner);
            return owner->value;
        }
    "#;
    let click_source = r#"
        verifying "touch_other.c";
        verifying "pipeline.c";

        void touch_other(struct cell* owner) {
            owns object(owner);
            mutable owner->other;
            ensures owner->other == 0;
        } by {
            execute();
            frame();
            simp();
        }

        int32 pipeline(struct cell* owner) {
            owns object(owner);
            mutable object(owner);
            ensures result == 11;
        } by {
            step();
            mark after_write;
            execute();
            transport(
                at(after_write, owner->value == 11),
                owner->value == 11
            );
            frame() using {};
            simp();
        }
    "#;
    let sources = [("touch_other.c", touch_c), ("pipeline.c", pipeline_c)];

    verify_c0_sources(click_source, &sources)
        .expect("the smart marked transport should verify before expansion");
    let selected = click_source.find("transport(").unwrap();
    let position = expansion::position_at_offset(click_source, selected);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("the marked transport should expand and replay");
    assert!(
        expanded
            .contains("transport(at(after_write, owner->value == 11), owner->value == 11) using {")
    );
    verify_c0_sources(&expanded, &sources).expect("the expanded marked transport should replay");

    let mutating_c = touch_c.replace("owner->other = 0;", "owner->value = 0;");
    let mutating_click = click_source.replace(
        "mutable owner->other;\n            ensures owner->other == 0;",
        "mutable owner->value;\n            ensures owner->value == 0;",
    );
    let error = verify_c0_sources(
        &mutating_click,
        &[
            ("touch_other.c", mutating_c.as_str()),
            ("pipeline.c", pipeline_c),
        ],
    )
    .expect_err("transport across mutation of the marked field must fail");
    assert!(
        error
            .message()
            .contains("no certified frame transport applies to the exact source fact"),
        "{}",
        error.message()
    );
}

#[test]
fn post_execution_store_transport_expands_from_the_recorded_store_equation() {
    let c_source = r#"
        int32 store_both(int32 p[2]) {
            p[0] = 7;
            p[1] = 9;
            return 0;
        }
    "#;
    let click_source = r#"
        verifying "store_both.c";

        int32 store_both(int32 p[2]) {
            consumes p[0..2];
            mutable p[0..2];
            produces p[0..2];
            ensures p[0] == 7;
        } by {
            execute();
            transport(
                at(statement(0).exit, p[0]) == 7,
                p[0] == 7
            );
            frame();
            simp();
        }
    "#;
    let sources = [("store_both.c", c_source)];

    verify_c0_sources(click_source, &sources)
        .expect("the post-execution store transport should verify");
    let selected = click_source.find("transport(").unwrap();
    let position = expansion::position_at_offset(click_source, selected);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("the store transport should expand from its recorded equation");
    assert!(expanded.contains("transport(") && expanded.contains("using {"));
    assert_eq!(
        expanded.matches("at(statement(0).exit, p[0]) == 7").count(),
        1,
        "the transport source must not be duplicated as an auxiliary premise:\n{expanded}"
    );
    verify_c0_sources(&expanded, &sources)
        .expect("the expanded store transport certificate should replay from a fresh parse");
}

#[test]
fn statement_snapshots_support_complete_loadability_propositions() {
    let c_source = r#"
            int32 store_second_return_first(int32 p[2]) {
                p[1] = 9;
                return p[0];
            }
        "#;
    let click_source = r#"
            verifying "snapshot_loadable.c";

            int32 store_second_return_first(int32 p[2]) {
                consumes p[0..2];
                mutable p[1..2];
                produces p[0..2];
                ensures result == p[0];
            } by {
                step();
                have at(statement(0).entry, loadable(p[0..2])) by {
                    assumption();
                }
                transport(
                    at(statement(0).entry, loadable(p[0..2])),
                    loadable(p[0..2])
                ) using {
                    at(statement(0).entry, loadable(p[0..2]));
                }
                execute();
                frame();
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("snapshot_loadable.c", c_source)])
        .expect("a complete loadability proposition should lower and transport from a snapshot");
}

#[test]
fn statement_snapshots_preserve_declared_resource_argument_types() {
    let c_source = r#"
            int32 preserve_owner(int32* owner) {
                return owner[0];
            }
        "#;
    let click_source = r#"
            resource owner_cell(owner: int32*) {
                owns owner[0..1];
            }

            verifying "snapshot_resource.c";

            int32 preserve_owner(int32* owner) {
                consumes owner_cell(owner);
                produces owner_cell(owner);
                ensures result == owner[0];
            } by {
                unfold(owner_cell(owner));
                execute();
                have at(
                    statement(0).entry,
                    contains(owner_cell(owner), memory(owner[0..1]))
                ) by {
                    assumption();
                }
                fold(owner_cell(owner));
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("snapshot_resource.c", c_source)])
        .expect("a historical resource proposition should retain declared argument types");
}

#[test]
fn source_expander_locates_frontier_local_have_proofs() {
    let c_source = r#"
            int32 preserve_value(int32 x) {
                x = x;
                return x;
            }
        "#;
    let click_source = r#"
            verifying "statement_assert.c";

            int32 preserve_value(int32 x) {
                ensures result == x;
            } by {
                have x == x by auto;
                execute();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have x == x by auto")
        .expect("frontier-local proof should exist");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("statement_assert.c", c_source)],
        line,
        column,
    )
    .expect("the frontier-local `have` proof should expand");
    assert_ne!(expanded, click_source);
    verify_c0_sources(&expanded, &[("statement_assert.c", c_source)])
        .expect("the expanded frontier-local proof should replay");
}

#[test]
fn smart_apply_uses_ambient_loadability_only_for_argument_lowering() {
    let c_source = r#"
            struct pointer_pair {
                int32* first;
                int32* second;
            };

            int32 pointer_pipeline(struct pointer_pair* pair, int32* data) {
                return 0;
            }
        "#;
    let click_source = r#"
            theorem pointer_equality_transitive(
                first: int32*,
                second: int32*,
                third: int32*
            ) {
                requires first == second;
                requires second == third;
                ensures first == third by {
                    simp();
                }
            }

            resource linked_pair(pair: struct pointer_pair*, data: int32*) {
                owns pair[0..4];
                fact pair->first == pair->second;
                fact pair->second == data;
            }

            verifying "pointer_pipeline.c";

            int32 pointer_pipeline(struct pointer_pair* pair, int32* data) {
                views linked_pair(pair, data);
                immutable;
                ensures result == 0;
            } by {
                observe(linked_pair(pair, data));
                apply(pointer_equality_transitive(
                    pair->first,
                    pair->second,
                    data
                ));
                execute();
                frame();
                simp();
            }
        "#;
    let apply_offset = click_source
        .find("apply(pointer_equality_transitive")
        .expect("proof should contain the selected apply");
    let line = click_source[..apply_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = apply_offset
        - click_source[..apply_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("pointer_pipeline.c", c_source)],
        line,
        column,
    )
    .expect("pointer theorem arguments should lower from the ambient loadability context");
    assert!(
        expanded.contains("apply(pointer_equality_transitive(") && expanded.contains(" using {"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("pointer_pipeline.c", c_source)])
        .expect("explicit theorem premises should replay with ambient argument lowering");
}

#[test]
fn selected_branched_post_execution_apply_merges_path_certificates() {
    let c_source = r#"
            int32 choose(int32 flag) {
                if (flag) {
                    return 1;
                } else {
                    return 2;
                }
            }
        "#;
    let click_source = r#"
            theorem retain_one_or_two(value: int32) {
                requires value == 1 or value == 2;
                ensures value == 1 or value == 2 by {
                    assumption();
                }
            }

            verifying "choose.c";

            int32 choose(int32 flag) {
                ensures result == 1 or result == 2;
            } by {
                execute();
                apply(retain_one_or_two(result));
                simp();
            }
        "#;
    let apply_offset = click_source
        .find("apply(retain_one")
        .expect("proof should contain the selected apply");
    let line = click_source[..apply_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = apply_offset
        - click_source[..apply_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("choose.c", c_source)], line, column)
            .expect("branched post-execution apply should produce path certificates");
    assert!(!expanded.contains("apply(retain_one_or_two(result));"));
    assert!(
        expanded.contains("if at(function.entry, flag) != at(function.entry, 0) {"),
        "{expanded}"
    );
    assert_eq!(
        expanded
            .matches("apply(retain_one_or_two(result)) using {")
            .count(),
        2,
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("choose.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "branched post-execution apply certificates should replay: {}\n{expanded}",
            error.message()
        )
    });
}

#[test]
fn selected_branched_post_execution_have_merges_path_certificates() {
    let c_source = r#"
            int32 choose(int32 flag) {
                if (flag) {
                    return 1;
                } else {
                    return 2;
                }
            }
        "#;
    let click_source = r#"
            verifying "choose.c";

            int32 choose(int32 flag) {
                ensures result == 1 or result == 2;
            } by {
                execute();
                have result == 1 or result == 2 by simp;
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have result")
        .expect("proof should contain the selected have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("choose.c", c_source)], line, column)
            .expect("branched post-execution have should produce path certificates");
    assert!(!expanded.contains("have result == 1 or result == 2 by simp"));
    assert!(
        expanded.contains("if at(function.entry, flag) != at(function.entry, 0) {"),
        "{expanded}"
    );
    assert_eq!(
        expanded
            .matches("have result == 1 or result == 2 by {")
            .count(),
        2,
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("choose.c", c_source)])
        .expect("branched post-execution have certificates should replay");
}

#[test]
fn selected_pure_case_split_simp_expands_by_removal() {
    // A smart exit `simp` whose claims all close by exact checks contributes
    // no surface tactics of its own. Its expansion must remove the tactic —
    // NOT graft the enclosing branch skeleton as an `if` tree with empty
    // leaves: that tree would re-split every already-merged execution path at
    // path end and lose the execution-path/branch-trace pairing certificate
    // replay keeps (git history (case-split expansion merge, 2026-07-31)).
    let c_source = r#"
            int32 sort3(int32 p[3]) {
                int32 tmp;
                if (p[1] < p[0]) {
                    tmp = p[0];
                    p[0] = p[1];
                    p[1] = tmp;
                }
                if (p[2] < p[1]) {
                    tmp = p[1];
                    p[1] = p[2];
                    p[2] = tmp;
                }
                if (p[1] < p[0]) {
                    tmp = p[0];
                    p[0] = p[1];
                    p[1] = tmp;
                }
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "sort3.c";

            predicate sorted_range(p: int32[], lo: int32, hi: int32) {
                forall (i: int32) {
                    forall (j: int32) {
                        0 <= i and 0 <= j and lo <= i and i < j and j < hi implies p[i] <= p[j]
                    }
                }
            }

            int32 sort3(int32 p[3]) {
                requires loadable(p[0..3]);
                consumes p[0..3];
                ensures sorted: sorted_range(p, 0, 3) by {
                    execute();
                    unfold(sorted_range);
                    simp();
                }
            }
        "#;
    let simp_offset = click_source
        .find("simp();")
        .expect("proof should contain the selected simp");
    let line = click_source[..simp_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = simp_offset
        - click_source[..simp_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[("sort3.c", c_source)], line, column)
        .expect("a pure case-split simp should expand");
    assert!(!expanded.contains("simp()"), "{expanded}");
    assert!(!expanded.contains("if p[1] < p[0] {"), "{expanded}");
    verify_c0_sources(&expanded, &[("sort3.c", c_source)])
        .expect("the removed closer's paths should close via the ordinary path-end check");
}

#[test]
fn source_expander_lowers_smart_simp_inside_have() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                have x == x by simp;
                execute();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have x == x")
        .expect("proof should contain the selected have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("the selected smart have should expand");
    let expanded_have = &expanded[expanded
        .find("have x == x")
        .expect("expanded proof should retain the selected have")
        ..expanded
            .find("execute()")
            .expect("expanded proof should retain its suffix")];
    assert!(expanded_have.contains("normalize();"), "{expanded_have}");
    assert!(!expanded_have.contains("simp();"), "{expanded_have}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the expanded smart have should replay");
}

#[test]
fn restricted_simp_expands_to_explicit_equality_rewrites() {
    let click_source = r#"
            theorem equality_transitive(x: int32, y: int32, z: int32) {
                requires x == y;
                requires y == z;
                ensures x == z by {
                    simp() using {
                        x == y;
                        y == z;
                    }
                }
            }
        "#;
    let offset = click_source
        .find("simp() using")
        .expect("proof should contain restricted simp");
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("restricted simp should expand");
    assert!(expanded.contains("rewrite(x == y);"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[]).expect("explicit equality certificate should replay");
}

#[test]
fn restricted_simp_after_unfold_expands_explicit_conjunction_extraction() {
    let click_source = r#"
            predicate equality_chain(x: int32, y: int32, z: int32) {
                x == y and y == z
            }

            theorem equality_transitive_after_unfold(x: int32, y: int32, z: int32) {
                requires equality_chain(x, y, z);
                ensures x == z by {
                    unfold(equality_chain);
                    simp() using {
                        x == y;
                        y == z;
                    }
                }
            }
        "#;
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("conjunction elimination should have an explicit expansion");
    assert!(expanded.contains("extract(x == y);"), "{expanded}");
    assert!(expanded.contains("extract(y == z);"), "{expanded}");
    assert!(expanded.contains("rewrite(x == y);"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[])
        .expect("explicit conjunction-elimination certificate should replay");
}

#[test]
fn restricted_simp_expands_strict_order_to_nonstrict_theorem_application() {
    let click_source = r#"
            theorem strict_order_implies_nonstrict(x: int32, y: int32) {
                requires x < y;
                ensures x <= y by {
                    simp() using {
                        x < y;
                    }
                }
            }
        "#;
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("strict-to-nonstrict simp should have an explicit certificate");
    assert!(
        expanded.contains("apply(int32_lt_implies_le(x, y)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded strict-order proof should replay");
}

#[test]
fn post_execution_simp_applies_strict_order_rule() {
    let c_source = r#"
        int32 identity(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "identity.c";

        int32 identity(int32 x) {
            requires x < 10;
            ensures result <= 10;
        } by {
            execute();
            simp();
        }
    "#;
    let offset = click_source.rfind("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("identity.c", c_source)],
        line,
        column,
    )
    .expect("post-execution strict-order simp should expand");
    assert!(
        expanded.contains("apply(int32_lt_implies_le("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("expanded post-execution strict-order proof should replay");
}

#[test]
fn restricted_simp_expands_negated_strict_order_to_greater_equal() {
    let click_source = r#"
        theorem not_negative_is_nonnegative(x: int32) {
            requires not (x < 0);
            ensures x >= 0 by {
                simp() using {
                    not (x < 0);
                }
            }
        }
    "#;
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("negated strict-order simp should expand");
    assert!(
        expanded.contains("apply(int32_not_lt_implies_ge(x, 0)) using"),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded negated-order proof should replay");
}

#[test]
fn post_execution_simp_expands_successor_strict_increase() {
    let c_source = r#"
        int32 increment(int32 x) {
            return x + 1;
        }
    "#;
    let click_source = r#"
        verifying "increment.c";

        int32 increment(int32 x) {
            requires x < 2147483647;
            ensures x < result;
        } by {
            execute();
            simp();
        }
    "#;
    let offset = click_source.rfind("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("increment.c", c_source)],
        line,
        column,
    )
    .expect("post-execution successor proof should expand");
    assert!(
        expanded.contains("apply(int32_increment_strictly_increases("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("increment.c", c_source)])
        .expect("expanded successor proof should replay");
}

#[test]
fn post_execution_simp_expands_increment_lower_bound() {
    let c_source = r#"
        int32 increment_nonnegative(int32 x) {
            return x + 1;
        }
    "#;
    let click_source = r#"
        verifying "increment_nonnegative.c";

        int32 increment_nonnegative(int32 x) {
            requires 0 <= x;
            requires x < 2147483647;
            ensures 0 <= result;
        } by {
            execute();
            simp();
        }
    "#;
    let offset = click_source.rfind("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("increment_nonnegative.c", c_source)],
        line,
        column,
    )
    .expect("post-execution increment lower bound should expand");
    assert!(
        expanded.contains("apply(int32_increment_lower_bound("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("increment_nonnegative.c", c_source)])
        .expect("expanded increment lower-bound proof should replay");
}

#[test]
fn post_execution_simp_expands_order_equality_closure() {
    let c_source = r#"
        int32 identity_at_bound(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "identity_at_bound.c";

        int32 identity_at_bound(int32 x) {
            requires x <= 1;
            requires not (x < 1);
            ensures result == 1;
        } by {
            execute();
            simp();
        }
    "#;
    let offset = click_source.rfind("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("identity_at_bound.c", c_source)],
        line,
        column,
    )
    .expect("post-execution order equality should expand");
    assert!(
        expanded.contains("apply(int32_le_and_not_lt_implies_eq("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity_at_bound.c", c_source)])
        .expect("expanded order-equality proof should replay");
}

#[test]
fn restricted_simp_expands_increment_upper_bound_to_theorem_application() {
    let click_source = r#"
        theorem increment_stays_bounded(value: int32, upper: int32) {
            requires value < upper;
            ensures value + 1 <= upper by {
                simp() using {
                    value < upper;
                }
            }
        }
    "#;
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("increment upper-bound simp should expand");
    assert!(
        expanded.contains("apply(int32_increment_upper_bound(value, upper)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("value < upper;"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should replay");
}

#[test]
fn restricted_simp_expands_positive_to_nonnegative_theorem_application() {
    let click_source = r#"
        theorem positive_is_nonnegative(value: int32) {
            requires 1 <= value;
            ensures 0 <= value by {
                simp() using {
                    1 <= value;
                }
            }
        }
    "#;
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("positive-to-nonnegative simp should expand");
    assert!(
        expanded.contains("apply(int32_positive_is_nonnegative(value)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("1 <= value;"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should replay");
}

#[test]
fn restricted_simp_expands_positive_predecessor_to_theorem_application() {
    let click_source = r#"
        theorem positive_predecessor_is_nonnegative(value: int32) {
            requires 0 < value;
            ensures 0 <= value - 1 by {
                simp() using {
                    0 < value;
                }
            }
        }
    "#;
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("positive-predecessor simp should expand");
    assert!(
        expanded.contains("apply(int32_positive_predecessor_is_nonnegative(value)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("0 < value;"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should replay");
}

#[test]
fn restricted_simp_expands_positive_predecessor_decrease_to_theorem_application() {
    let click_source = r#"
        theorem positive_predecessor_decreases(value: int32) {
            requires 0 < value;
            ensures value - 1 < value by {
                simp() using {
                    0 < value;
                }
            }
        }
    "#;
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("positive-predecessor decrease simp should expand");
    assert!(
        expanded
            .contains("apply(int32_positive_predecessor_strictly_decreases(value)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("0 < value;"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should replay");
}

#[test]
fn restricted_simp_expands_strict_increment_to_theorem_application() {
    let click_source = r#"
            theorem increment_is_greater(value: int32, upper: int32) {
                requires value < upper;
                ensures value < value + 1 by {
                    simp() using {
                        value < upper;
                    }
                }
            }
        "#;
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("strict increment should expand");
    assert!(
        expanded.contains("apply(int32_increment_strictly_increases(value, upper)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("value < upper;"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[]).expect("strict increment certificate should replay");
}

#[test]
fn restricted_simp_expands_increment_lower_bound_to_theorem_application() {
    let click_source = r#"
        theorem increment_preserves_lower_bound(
            value: int32,
            lower: int32,
            upper: int32
        ) {
            requires lower <= value;
            requires value < upper;
            ensures lower <= value + 1 by {
                simp() using {
                    lower <= value;
                    value < upper;
                }
            }
        }
    "#;
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("increment lower-bound simp should expand");
    assert!(
        expanded.contains("apply(int32_increment_lower_bound(value, lower, upper)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("lower <= value;"), "{expanded}");
    assert!(expanded.contains("value < upper;"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should replay");
}

#[test]
fn restricted_simp_expands_increment_order_to_theorem_application() {
    let click_source = r#"
        theorem increment_preserves_order(
            value: int32,
            lower: int32,
            upper: int32
        ) {
            requires lower <= value;
            requires value < upper;
            ensures lower + 1 <= value + 1 by {
                simp() using {
                    lower <= value;
                    value < upper;
                }
            }
        }
    "#;
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("increment order simp should expand");
    assert!(
        expanded.contains("apply(int32_increment_preserves_order(value, lower, upper)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("lower <= value;"), "{expanded}");
    assert!(expanded.contains("value < upper;"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should replay");
}

#[test]
fn restricted_simp_expands_adjacent_order_to_theorem_application() {
    let click_source = r#"
        theorem two_at_most_implies_one_below(value: int32) {
            requires 2 <= value;
            ensures 1 < value by {
                simp() using {
                    2 <= value;
                }
            }
        }
    "#;
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("adjacent order simp should expand");
    assert!(
        expanded.contains("apply(int32_successor_le_implies_lt(1, value)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("2 <= value;"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should replay");
}

#[test]
fn restricted_simp_composes_equality_rewrites_with_adjacent_order() {
    let click_source = r#"
        theorem aliased_positive_bound(
            position: int32,
            bound: int32,
            length: int32
        ) {
            requires 1 <= length;
            requires bound == length;
            requires position == 0;
            ensures position < bound by {
                simp() using {
                    1 <= length;
                    bound == length;
                    position == 0;
                }
            }
        }
    "#;
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("rewrites followed by adjacent order should expand");
    assert!(expanded.contains("rewrite(bound == length);"), "{expanded}");
    assert!(expanded.contains("rewrite(position == 0);"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_successor_le_implies_lt(0, length)) using"),
        "{expanded}"
    );
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("composed explicit certificate should replay");
}

#[test]
fn restricted_simp_inside_have_expands_to_explicit_equality_rewrites() {
    let c_source = r#"
            int32 identity(int32 x, int32 y, int32 z) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x, int32 y, int32 z) {
                requires x == y;
                requires y == z;
                ensures result == x;
            } by {
                have x == z by {
                    simp() using {
                        x == y;
                        y == z;
                    }
                }
                execute();
                simp();
            }
        "#;
    let offset = click_source
        .find("have x == z")
        .expect("proof should contain restricted simp have");
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("restricted simp have should expand");
    let expanded_have =
        &expanded[expanded.find("have x == z").unwrap()..expanded.find("execute();").unwrap()];
    assert!(
        expanded_have.contains("rewrite(x == y);"),
        "{expanded_have}"
    );
    assert!(expanded_have.contains("assumption();"), "{expanded_have}");
    assert!(!expanded_have.contains("simp() using"), "{expanded_have}");
    assert!(!expanded_have.contains("derive using"), "{expanded_have}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("explicit equality have certificate should replay");
}

#[test]
fn restricted_simp_expands_loadable_subrange_to_explicit_transport() {
    let c_source = r#"
        int32 read_at(int32 data[], int32 index, int32 length) {
            return data[index];
        }
    "#;
    let click_source = r#"
        verifying "read_at.c";

        int32 read_at(int32 data[], int32 index, int32 length) {
            requires 0 <= index;
            requires index < length;
            requires loadable(data[0..length]);
            views data[0..length];
            ensures result == old(data[index]);
        } by {
            have loadable(data[index..index + 1]) by {
                simp() using {
                    loadable(data[0..length]);
                    0 <= index;
                    index < length;
                }
            }
            execute();
            simp();
        }
    "#;
    let offset = click_source
        .find("have loadable(data[index..index + 1])")
        .unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let sources = [("read_at.c", c_source)];

    let expanded = expand_c0_tactic_source_at(click_source, &sources, line, column)
        .expect("restricted simp loadability proof should expand");
    let expanded_have_start = expanded.find("have loadable(").unwrap();
    let expanded_have_end = expanded[expanded_have_start..]
        .find("execute();")
        .map(|relative| expanded_have_start + relative)
        .unwrap();
    let expanded_have = &expanded[expanded_have_start..expanded_have_end];
    assert!(
        expanded_have.contains(
            "transport(loadable(data[0..length]), loadable(data[index..(index + 1)])) using"
        ),
        "{expanded_have}"
    );
    assert!(expanded_have.contains("0 <= index;"), "{expanded_have}");
    assert!(expanded_have.contains("index < length;"), "{expanded_have}");
    assert!(expanded_have.contains("assumption();"), "{expanded_have}");
    assert!(!expanded_have.contains("simp() using"), "{expanded_have}");
    assert!(!expanded_have.contains("derive using"), "{expanded_have}");
    verify_c0_sources(&expanded, &sources).expect("explicit loadability transport should replay");
}

#[test]
fn restricted_simp_rewrites_pointer_aliases_inside_memory_loads() {
    let c_source = r#"
        int32 alias_value(
            int32 original[],
            int32 alias[],
            int32 index,
            int32 length,
            int32 value
        ) {
            return value;
        }
    "#;
    let click_source = r#"
        verifying "alias_value.c";

        resource valued_array(data: int32*, length: int32, value: int32) {
            owns data[0..length];
            fact 1 <= length;
            fact data[0] == value;
        }

        int32 alias_value(
            int32 original[],
            int32 alias[],
            int32 index,
            int32 length,
            int32 value
        ) {
            requires index == 0;
            requires alias == original;
            owns valued_array(original, length, value);
            ensures alias[index] == value;
        } by {
            unfold(valued_array(original, length, value));
            step();
            have alias[index] == value by {
                simp() using {
                    original[0] == value;
                    alias == original;
                    index == 0;
                }
            }
            fold(valued_array(original, length, value));
            simp();
        }
    "#;
    let offset = click_source.find("have alias[index] == value").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let sources = [("alias_value.c", c_source)];

    let expanded = expand_c0_tactic_source_at(click_source, &sources, line, column)
        .expect("pointer-alias restricted simp should expand");
    let expanded_have_start = expanded.find("have alias[index] == value").unwrap();
    let expanded_have_end = expanded[expanded_have_start..]
        .find("fold(valued_array")
        .map(|relative| expanded_have_start + relative)
        .unwrap();
    let expanded_have = &expanded[expanded_have_start..expanded_have_end];
    assert!(
        expanded_have.contains("rewrite(alias == original);"),
        "{expanded_have}"
    );
    assert!(
        expanded_have.contains("rewrite(index == 0);"),
        "{expanded_have}"
    );
    assert!(
        expanded_have.contains("rewrite(value == original[0]);"),
        "{expanded_have}"
    );
    assert!(expanded_have.contains("normalize();"), "{expanded_have}");
    assert!(!expanded_have.contains("derive using"), "{expanded_have}");
    verify_c0_sources(&expanded, &sources)
        .expect("expanded pointer-alias certificate should replay");
}

#[test]
fn post_execution_restricted_simp_expands_without_derive() {
    let c_source = r#"
        int32 identity(int32 x, int32 y, int32 z) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "identity.c";

        int32 identity(int32 x, int32 y, int32 z) {
            requires x + 1 == y;
            requires y == z;
            ensures result + 1 == z;
        } by {
            execute();
            have x + 1 == z by {
                simp() using {
                    x + 1 == y;
                    y == z;
                }
            }
            simp();
        }
    "#;
    let offset = click_source.find("have x + 1 == z").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let sources = [("identity.c", c_source)];
    let expanded = expand_c0_tactic_source_at(click_source, &sources, line, column).unwrap();
    let selected = &expanded[offset..expanded.find("assumption();").unwrap()];
    assert!(selected.contains("rewrite((x + 1) == y);"), "{selected}");
    assert!(!selected.contains("derive using"), "{selected}");
    verify_c0_sources(&expanded, &sources).expect("explicit post-execution proof should replay");
}

#[test]
fn source_expander_lowers_smart_apply_inside_have() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            theorem int32_reflexive(value: int32) {
                ensures value == value by {
                    simp();
                }
            }

            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                have x == x by {
                    apply(int32_reflexive(x));
                }
                execute();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have x == x")
        .expect("proof should contain the selected have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("the selected smart apply inside have should expand");
    let expanded_have = &expanded[expanded
        .find("have x == x")
        .expect("expanded proof should retain the selected have")
        ..expanded
            .find("execute()")
            .expect("expanded proof should retain its suffix")];
    assert!(expanded_have.contains("apply(int32_reflexive(x)) using {"));
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the expanded smart apply inside have should replay");
}

#[test]
fn source_expander_lowers_smart_simp_after_unfold_inside_have() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            predicate reflexive(x: int32) {
                x == x
            }

            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                have reflexive(x) by {
                    unfold(reflexive);
                    simp();
                }
                execute();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have reflexive(x)")
        .expect("proof should contain the selected have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("the selected unfolded smart have should expand");
    let expanded_have = &expanded[expanded
        .find("have reflexive(x)")
        .expect("expanded proof should retain the selected have")
        ..expanded
            .find("execute()")
            .expect("expanded proof should retain its suffix")];
    assert!(
        expanded_have.contains("unfold(reflexive);"),
        "{expanded_have}"
    );
    assert!(expanded_have.contains("normalize();"), "{expanded_have}");
    assert!(!expanded_have.contains("simp();"), "{expanded_have}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the expanded unfolded smart have should replay");
}

#[test]
fn source_expander_extracts_unfolded_conjuncts_inside_have() {
    let c_source = r#"
            int32 identity(int32 x, int32 y, int32 z) {
                return x;
            }
        "#;
    let click_source = r#"
            predicate equality_chain(x: int32, y: int32, z: int32) {
                x == y and y == z
            }

            verifying "identity.c";

            int32 identity(int32 x, int32 y, int32 z) {
                requires equality_chain(x, y, z);
                ensures result == x;
            } by {
                have x == z by {
                    unfold(equality_chain);
                    simp() using {
                        x == y;
                        y == z;
                    }
                }
                execute();
                simp();
            }
        "#;
    let offset = click_source.find("have x == z").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("restricted simp should extract its unfolded conjunct premises");
    assert!(expanded.contains("extract(x == y);"), "{expanded}");
    assert!(expanded.contains("extract(y == z);"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("expanded point-proof conjunction extraction should replay");
}

#[test]
fn source_expander_preserves_pointer_field_spelling_inside_smart_have() {
    let c_source = r#"
            struct holder {
                int32* data;
            };

            int32 holder_zero(struct holder* owner, int32 data[]) {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "holder.c";

            int32 holder_zero(struct holder* owner, int32 data[]) {
                requires owner->data == data;
                views object(owner);
                immutable;
                ensures result == 0;
            } by {
                have owner->data == data by simp;
                execute();
                frame();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have owner->data == data")
        .expect("proof should contain the selected pointer have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("holder.c", c_source)], line, column)
            .expect("the pointer-valued smart have should expand");
    assert!(
        expanded.contains("have owner->data == data by {"),
        "{expanded}"
    );
    assert!(expanded.contains("assumption();"), "{expanded}");
    verify_c0_sources(&expanded, &[("holder.c", c_source)])
        .expect("the expanded pointer-valued have should replay");
}

#[test]
fn source_expander_spells_an_indexed_load_through_a_pointer_field() {
    let c_source = r#"
            struct holder {
                int32* data;
            };

            int32 holder_read(struct holder* owner, int32 data[], int32 value) {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "holder.c";

            predicate second_is(owner: struct holder*, value: int32) {
                owner->data[1] == value
            }

            int32 holder_read(
                struct holder* owner,
                int32 data[],
                int32 value
            ) {
                requires owner->data == data;
                requires separate(memory(object(owner)), memory(data[1..2]));
                requires second_is(owner, value);
                views object(owner);
                views data[1..2];
                immutable;
                ensures result == 0;
            } by {
                unfold(second_is);
                have data[1] == value by simp;
                execute();
                frame();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have data[1] == value")
        .expect("proof should contain the selected indexed have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("holder.c", c_source)], line, column)
            .expect("the indexed pointer-field fact should have a surface spelling");
    assert!(expanded.contains("owner->data[1] == value"), "{expanded}");
    verify_c0_sources(&expanded, &[("holder.c", c_source)])
        .expect("the indexed pointer-field expansion should replay");
}

#[test]
fn smart_have_uses_transport_planned_at_the_mutation_boundary() {
    let c_source = r#"
            int32 set_second_return_first(int32 p[2]) {
                p[1] = 9;
                return p[0];
            }
        "#;
    let click_source = r#"
            verifying "transport.c";

            predicate first_is_seven(p: int32[]) {
                p[0] == 7
            }

            int32 set_second_return_first(int32 p[2]) {
                requires first_is_seven(p);
                consumes p[0..2];
                mutable p[1..2] by {
                    unfold(first_is_seven);
                    step();
                    have p[0] == 7 by simp;
                    step();
                    frame();
                }
                produces p[0..2];
            }
        "#;
    let have_offset = click_source
        .find("have p[0] == 7")
        .expect("proof should contain the selected have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("transport.c", c_source)], line, column)
            .expect("the transported current-state fact should expand as an assumption");
    let expanded_have = &expanded[expanded
        .find("have p[0] == 7")
        .expect("expanded proof should retain the selected have")
        ..expanded
            .find("step();\n                    frame();")
            .expect("expanded proof should retain its suffix")];
    assert!(expanded_have.contains("assumption();"), "{expanded_have}");
    assert!(!expanded_have.contains("transport("), "{expanded_have}");
    assert!(!expanded_have.contains("simp();"), "{expanded_have}");
    verify_c0_sources(&expanded, &[("transport.c", c_source)])
        .expect("the expansion should replay using the transport planned by the prior statement");
}

#[test]
fn smart_have_uses_fact_selected_by_explicit_step_at_the_mutation_boundary() {
    let c_source = r#"
            int32 set_second_return_first(int32 p[2]) {
                p[1] = 9;
                return p[0];
            }
        "#;
    let click_source = r#"
            verifying "transport.c";

            predicate first_is_seven(p: int32[]) {
                p[0] == 7
            }

            int32 set_second_return_first(int32 p[2]) {
                requires first_is_seven(p);
                consumes p[0..2];
                mutable p[1..2] by {
                    unfold(first_is_seven);
                    step() using {
                        p[0] == 7;
                        loadable(p[0..2]);
                    }
                    have p[0] == 7 by simp;
                    step();
                    frame();
                }
                produces p[0..2];
            }
        "#;
    let have_offset = click_source
        .find("have p[0] == 7")
        .expect("proof should contain the selected have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("transport.c", c_source)], line, column)
            .expect("the fact selected by `step() using` should reach the current snapshot");
    let expanded_have = &expanded[expanded
        .find("have p[0] == 7")
        .expect("expanded proof should retain the selected have")
        ..expanded
            .find("step();\n                    frame();")
            .expect("expanded proof should retain its suffix")];
    assert!(expanded_have.contains("assumption();"), "{expanded_have}");
    assert!(!expanded_have.contains("simp();"), "{expanded_have}");
    verify_c0_sources(&expanded, &[("transport.c", c_source)])
        .expect("the explicit-step boundary transport should replay");
}

#[test]
fn source_expander_recalls_a_fact_at_a_recorded_statement_entry() {
    let preserve_c_source = r#"
            int32 preserve(int32 p[1]) {
                return p[0];
            }
        "#;
    let pipeline_c_source = r#"
            int32 pipeline(int32 p[1]) {
                int32 ignored;
                ignored = preserve(p);
                return p[0];
            }
        "#;
    let click_source = r#"
            verifying "preserve.c";
            verifying "snapshot.c";

            resource one(p: int32*) {
                owns p[0..1];
                fact p[0] == 1;
            }

            int32 preserve(int32 p[1]) {
                views one(p);
                immutable;
                ensures result == 1;
            } by {
                observe(one(p));
                execute();
                frame();
                simp();
            }

            int32 pipeline(int32 p[1]) {
                views one(p);
                immutable;
                ensures result == 1;
            } by {
                observe(one(p));
                execute_until(statement(2));
                have at(statement(1).entry, p[0]) == 1 by simp;
                execute();
                frame();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have at(statement(1).entry")
        .expect("proof should contain the selected snapshot have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let c_sources = [
        ("preserve.c", preserve_c_source),
        ("snapshot.c", pipeline_c_source),
    ];
    let expanded = expand_c0_tactic_source_at(click_source, &c_sources, line, column)
        .expect("the snapshot have should expand");
    assert!(expanded.contains("assumption();"), "{expanded}");
    verify_c0_sources(&expanded, &c_sources).expect("the expanded snapshot have should replay");
}

#[test]
fn source_expander_derives_separation_from_call_postconditions() {
    let init_c_source = r#"
            struct cursor {
                int32 pos;
                int32 len;
                int32* data;
            };

            int32 init(struct cursor* owner, int32 data[], int32 length) {
                owner->pos = 0;
                owner->len = length;
                owner->data = data;
                return 0;
            }
        "#;
    let pipeline_c_source = r#"
            struct cursor {
                int32 pos;
                int32 len;
                int32* data;
            };

            int32 pipeline(
                struct cursor* left,
                struct cursor* right,
                int32 data[],
                int32 length
            ) {
                int32 ignored;
                ignored = init(left, data, length);
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "init.c";
            verifying "pipeline.c";

            int32 init(
                struct cursor* owner,
                int32 data[],
                int32 length
            ) {
                requires 0 <= length;
                requires separate(memory(owner[0..4]), memory(data[0..length]));
                consumes owner[0..4];
                views data[0..length];
                mutable owner[0..4];
                produces owner[0..4];
                ensures result == 0;
                ensures owner->pos == 0;
                ensures owner->len == length;
                ensures owner->data == data;
            } by {
                execute();
                frame();
                simp();
            }

            int32 pipeline(
                struct cursor* left,
                struct cursor* right,
                int32 data[],
                int32 length
            ) {
                requires 1 <= length;
                requires separate(memory(left[0..4]), memory(data[0..length]));
                requires separate(memory(right[0..4]), memory(data[0..length]));
                consumes left[0..4];
                consumes right[0..4];
                views data[0..length];
                mutable left[0..4], right[0..4];
                produces left[0..4];
                produces right[0..4];
                ensures result == 0;
            } by {
                execute_until(statement(2));
                have separate(
                    memory(right[0..4]),
                    memory(left->data[0..left->len])
                ) by {
                    simp();
                }
                execute();
                frame();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have separate(")
        .expect("proof should contain the selected separation have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let c_sources = [("init.c", init_c_source), ("pipeline.c", pipeline_c_source)];

    let expanded = expand_c0_tactic_source_at(click_source, &c_sources, line, column)
        .expect("call postconditions should expand into an explicit separation derivation");
    assert!(expanded.contains("left->len == length"), "{expanded}");
    assert!(expanded.contains("left->data == data"), "{expanded}");
    assert!(!expanded.contains("load_int32_pointer"), "{expanded}");
    assert!(expanded.contains("rewrite("), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &c_sources)
        .expect("the expanded separation derivation should replay");
}

#[test]
fn branched_smart_simp_expansion_replays_as_surface_click() {
    let c_source = r#"
            int32 choose(int32 flag) {
                if (flag) {
                    return 1;
                } else {
                    return 2;
                }
            }
        "#;
    let click_source = r#"
            verifying "choose.c";

            int32 choose(int32 flag) {
                ensures result == 1 or result == 2 by { execute(); simp(); }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("choose.c", c_source)])
        .expect("branched smart simp should verify");
    let expanded = verified[0]
        .expanded_proof_source()
        .expect("branched smart simp should lower to surface tactics");
    let expanded_source = click_source.replacen("by { execute(); simp(); }", &expanded, 1);
    verify_c0_sources(&expanded_source, &[("choose.c", c_source)])
        .expect("printed branched smart simp expansion should replay");
}

#[test]
fn source_expander_replaces_only_the_selected_claim_proof() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures first: result == x by { execute(); simp(); }
                ensures second: result == x + 0 by { execute(); simp(); }
            }
        "#;

    let expanded = expand_c0_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Ensure(1),
    )
    .expect("selected smart proof should expand");
    assert_eq!(expanded.matches("by { execute(); simp(); }").count(), 1);
    assert!(expanded.contains("ensures first: result == x by { execute(); simp(); }"));
    verify_c0_sources(&expanded, &[("identity.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "source-expanded sidecar should re-verify: {}\n{expanded}",
            error.message()
        )
    });
}

#[test]
fn source_expander_replaces_and_replays_grouped_proof() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures first: result == x;
                ensures second: result == x + 0;
            } by {
                execute();
                simp();
            }
        "#;

    let expanded = expand_c0_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Grouped,
    )
    .expect("grouped proof should expand");
    assert!(!expanded.contains("execute();"));
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("expanded grouped proof should re-verify");
}

#[test]
fn source_expander_replaces_and_replays_contextual_frame() {
    let c_source = r#"
            int32 write_in_bounds(int32 p[], int32 i, int32 n) {
                p[i] = 9;
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "write_in_bounds.c";

            int32 write_in_bounds(int32 p[], int32 i, int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires i >= 0;
                requires i < n;
                consumes p[0..n];
                mutable p[0..n] by { execute(); frame(); }
            }
        "#;

    let expanded = expand_c0_claim_source(
        click_source,
        &[("write_in_bounds.c", c_source)],
        "write_in_bounds",
        CProofClaim::Effect(0),
    )
    .expect("contextual frame should expand");
    assert!(!expanded.contains("execute();"));
    verify_c0_sources(&expanded, &[("write_in_bounds.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "expanded contextual frame should re-verify: {}\n{expanded}",
            error.message()
        )
    });
}

#[test]
fn source_expander_shares_path_independent_frame_across_c_branches() {
    let c_source = r#"
            int32 write_by_flag(int32 p[], int32 flag) {
                if (flag == 0) {
                    p[0] = 1;
                } else {
                    p[0] = 2;
                }
                return p[0];
            }
        "#;
    let click_source = r#"
            verifying "write_by_flag.c";

            int32 write_by_flag(int32 p[], int32 flag) {
                consumes p[0..1];
                mutable p[0..1];
            } by {
                execute();
                frame();
            }
        "#;

    let frame_offset = click_source
        .find("frame();")
        .expect("proof should contain the selected frame");
    let position = expansion::position_at_offset(click_source, frame_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("write_by_flag.c", c_source)],
        position.line,
        position.column,
    )
    .expect("path-independent frame should expand across C branches");
    assert!(!expanded.contains("frame();"), "{expanded}");
    verify_c0_sources(&expanded, &[("write_by_flag.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "expanded path-independent frame should re-verify: {}\n{expanded}",
            error.message()
        )
    });
}

#[test]
fn source_expander_is_idempotent() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x by { execute(); simp(); }
            }
        "#;
    let sources = [("identity.c", c_source)];

    let expanded_once =
        expand_c0_claim_source(click_source, &sources, "identity", CProofClaim::Ensure(0))
            .expect("smart proof should expand");
    let expanded_twice =
        expand_c0_claim_source(&expanded_once, &sources, "identity", CProofClaim::Ensure(0))
            .expect("expanded proof should expand again");

    assert_eq!(expanded_once, expanded_twice);
}

#[test]
fn source_expander_replaces_and_replays_default_ensure_proof() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            }
        "#;

    let expanded_once = expand_c0_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Ensure(0),
    )
    .expect("default proof should expand");
    let expanded_twice = expand_c0_claim_source(
        &expanded_once,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Ensure(0),
    )
    .expect("explicit expansion should expand again");

    assert!(expanded_once.contains("ensures result == x by {"));
    assert_eq!(expanded_once, expanded_twice);
    verify_c0_sources(&expanded_once, &[("identity.c", c_source)])
        .expect("expanded default ensure should re-verify");
}

#[test]
fn source_expander_replaces_and_replays_default_effect_proof() {
    let c_source = r#"
            int32 zero() {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "zero.c";

            int32 zero() {
                immutable;
            }
        "#;
    let sources = [("zero.c", c_source)];

    let expanded_once =
        expand_c0_claim_source(click_source, &sources, "zero", CProofClaim::Effect(0))
            .expect("default effect proof should expand");
    let expanded_twice =
        expand_c0_claim_source(&expanded_once, &sources, "zero", CProofClaim::Effect(0))
            .expect("explicit effect expansion should expand again");

    assert!(expanded_once.contains("immutable by {"));
    assert_eq!(expanded_once, expanded_twice);
    verify_c0_sources(&expanded_once, &sources).expect("expanded default effect should re-verify");
}

#[test]
fn source_expander_reports_missing_grouped_proof_precisely() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            }
        "#;

    let error = expand_c0_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Grouped,
    )
    .expect_err("independent claims do not have a grouped proof");

    assert!(
        error
            .message()
            .contains("grouped verification but has no source `by` clause")
    );
}
