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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("checked post-execution smart have should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "surface certificate replay"
        )),
        "the result-aware smart have must retain its checked Proof: {events:#?}"
    );

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
fn post_execution_smart_have_applies_a_theorem_to_result_through_proof() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            theorem int32_reflexive(value: int32) {
                ensures value == value by {
                    normalize();
                }
            }

            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                execute();
                have result == result by {
                    apply(int32_reflexive(result));
                    simp();
                }
                simp();
            }
        "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("result-aware theorem application should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "surface certificate replay"
        )),
        "the result-aware theorem application must not reconstruct and replay a certificate: {events:#?}"
    );

    let have_offset = click_source
        .find("have result == result")
        .expect("proof should contain the result-aware have");
    let position = expansion::position_at_offset(click_source, have_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("identity.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained result-aware Proof should expand");
    let expanded_have_start = expanded
        .find("have result == result")
        .expect("expanded proof should retain the selected have");
    let expanded_have_end = expanded[expanded_have_start..]
        .find("\n                simp();")
        .map(|offset| expanded_have_start + offset)
        .expect("expanded proof should retain its outer closer");
    let expanded_have = &expanded[expanded_have_start..expanded_have_end];
    assert!(
        expanded_have.contains("apply(int32_reflexive(result)) using"),
        "{expanded_have}"
    );
    assert!(!expanded_have.contains("simp();"), "{expanded_have}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the expanded result-aware theorem application should independently verify");
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("checked post-execution transport should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "surface certificate replay"
        )),
        "the smart transport must retain its checked Proof: {events:#?}"
    );

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
fn grouped_post_execution_unfold_retains_its_checked_proof_step() {
    let c_source = r#"
        int32 identity(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        predicate selected(x: int32) {
            x == x
        }

        verifying "identity.c";

        int32 identity(int32 x) {
            requires selected(x);
            ensures selected(x);
        } by {
            execute();
            unfold(selected);
            assumption();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("the grouped outcome unfold should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "surface certificate replay"
        )),
        "the grouped outcome unfold must retain its checked Proof: {events:#?}"
    );
}

#[test]
fn grouped_post_execution_closers_use_independent_checked_proofs() {
    let c_source = r#"
        int32 identity(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "identity.c";

        int32 identity(int32 x) {
            requires selected: x == 0;
            ensures retained: x == 0;
            ensures reflexive: result == result;
        } by {
            execute();
            assumption();
            normalize();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("grouped outcome closers should verify through focused Proof roots");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "surface certificate replay"
        )),
        "grouped outcome closers must retain their checked Proof steps: {events:#?}"
    );
}

#[test]
fn post_execution_rewrite_retains_its_checked_proof_step() {
    let c_source = r#"
        int32 identity(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "identity.c";

        int32 identity(int32 x) {
            requires zero: x == 0;
            ensures successor: x + 1 == 1;
        } by {
            execute();
            rewrite(x == 0);
            normalize();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("outcome rewrite should advance its focused Proof goal");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "surface certificate replay"
        )),
        "outcome rewrite must retain its checked Proof step: {events:#?}"
    );
}

#[test]
fn grouped_post_execution_simp_publishes_checked_obligations_through_proof() {
    let c_source = r#"
        int32 identity(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "identity.c";

        int32 identity(int32 x) {
            ensures first: result == result;
            ensures second: result == result;
        } by {
            execute();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("grouped simp should retain its checked obligation scopes");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "surface certificate replay"
        )),
        "grouped direct simp must not construct and replay a second certificate: {events:#?}"
    );

    let simp_offset = click_source
        .find("simp();")
        .expect("proof should contain the selected grouped simp");
    let position = expansion::position_at_offset(click_source, simp_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("identity.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained grouped simp certificate should expand");
    assert_eq!(expanded.matches("have result == result by {").count(), 2);
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the serialized grouped obligation scopes should verify independently");
}

#[test]
fn grouped_post_execution_simp_applies_planned_steps_once_through_proof() {
    let c_source = r#"
        int32 identity(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "identity.c";

        int32 identity(int32 x) {
            requires zero: x == 0;
            ensures successor: x + 1 == 1;
        } by {
            execute();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("grouped simp should apply its planned rewrite through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "surface certificate replay"
        )),
        "a planner-selected grouped candidate must be checked once and retained: {events:#?}"
    );

    let simp_offset = click_source
        .find("simp();")
        .expect("proof should contain the selected grouped simp");
    let position = expansion::position_at_offset(click_source, simp_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("identity.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the planner-selected grouped certificate should expand");
    assert!(
        expanded.contains("rewrite(at(function.entry, x == 0));"),
        "{expanded}"
    );
    assert!(expanded.contains("normalize();"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the retained planner-selected steps should verify independently");
}

#[test]
fn post_execution_simp_builds_disjunction_cases_on_proof() {
    let c_source = r#"
        int32 choose(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "choose.c";

        int32 choose(int32 x) {
            requires x == 0 or x == 1;
            ensures 0 <= result;
        } by {
            execute();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("choose.c", c_source)])
    });
    verified.expect("the two-value result should prove nonnegative by cases");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp compatibility construction"
        )),
        "the checked Proof case split must bypass compatibility construction: {events:#?}"
    );

    let simp_offset = click_source
        .find("simp();")
        .expect("proof should contain the selected grouped simp");
    let position = expansion::position_at_offset(click_source, simp_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("choose.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the checked case split should expand");
    assert!(!expanded.contains("simp();"), "{expanded}");
    assert!(
        expanded.contains("cases (at(function.entry, x == 0 or x == 1))"),
        "{expanded}"
    );
    assert_eq!(expanded.matches("rewrite(").count(), 2, "{expanded}");
    assert_eq!(expanded.matches("normalize();").count(), 2, "{expanded}");
    verify_c0_sources(&expanded, &[("choose.c", c_source)])
        .expect("the retained case split should verify independently");
}

#[test]
fn symbolic_max_outcomes_retain_selected_branch_order_paths() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests")
        .join("max_symbolic.md");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("max_symbolic should contain Click source");
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &c_sources));
    verified.expect("both symbolic max claims should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp compatibility construction"
                    || name == "outcome simp legacy exit planning"
        )),
        "selected branch order paths must bypass outcome fallbacks: {events:#?}"
    );

    for claim in [CProofClaim::Ensure(0), CProofClaim::Ensure(1)] {
        let expanded = expand_c0_claim_source(click_source, &c_sources, "max", claim)
            .expect("the retained branch order proof should expand");
        verify_c0_sources(&expanded, &c_sources)
            .expect("the expanded branch order proof should replay independently");
    }
}

#[test]
fn outcome_arithmetic_normalization_retains_selected_equality_paths() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests")
        .join("later_loop_preserve.md");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("later_loop_preserve should contain Click source");
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &c_sources));
    verified.expect("the return expression should normalize through retained equalities");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp compatibility construction"
                    || name == "outcome simp legacy exit planning"
        )),
        "selected equality paths must bypass outcome fallbacks: {events:#?}"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &c_sources,
        "later_loop_preserve",
        CProofClaim::Ensure(0),
    )
    .expect("the retained equality paths should expand");
    assert!(expanded.matches("rewrite(").count() >= 2, "{expanded}");
    verify_c0_sources(&expanded, &c_sources)
        .expect("the expanded equality paths should replay independently");
}

#[test]
fn outcome_quantified_cells_retain_selected_instantiations() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests")
        .join("fill3_array_loop.md");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("fill3_array_loop should contain Click source");
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &c_sources));
    verified.expect("all three concrete cells should specialize the retained loop invariant");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp compatibility construction"
                    || name == "outcome simp legacy exit planning"
        )),
        "selected universal instances must bypass outcome fallbacks: {events:#?}"
    );

    for claim in [
        CProofClaim::Ensure(0),
        CProofClaim::Ensure(1),
        CProofClaim::Ensure(2),
    ] {
        let expanded = expand_c0_claim_source(click_source, &c_sources, "fill3_array_loop", claim)
            .expect("the retained universal instance should expand");
        assert!(expanded.contains("instantiate("), "{expanded}");
        verify_c0_sources(&expanded, &c_sources)
            .expect("the expanded universal instance should replay independently");
    }
}

#[test]
fn post_execution_simp_builds_recursive_conjunction_on_proof() {
    let c_source = r#"
        int32 first(int32 x, int32 y) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "first.c";

        int32 first(int32 x, int32 y) {
            requires 1 <= x;
            requires 1 <= y;
            ensures 0 <= x and 0 <= y;
        } by {
            execute();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("first.c", c_source)])
    });
    verified.expect("the conjunction should retain both recursively checked child proofs");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp compatibility construction"
        )),
        "recursive conjunction closure must bypass compatibility construction: {events:#?}"
    );

    let simp_offset = click_source
        .find("simp();")
        .expect("proof should contain the selected grouped simp");
    let position = expansion::position_at_offset(click_source, simp_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("first.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained conjunction should expand");
    assert!(!expanded.contains("simp();"), "{expanded}");
    assert_eq!(
        expanded
            .matches("apply(int32_positive_is_nonnegative(")
            .count(),
        2,
        "{expanded}"
    );
    assert!(expanded.contains("split();"), "{expanded}");
    verify_c0_sources(&expanded, &[("first.c", c_source)])
        .expect("the retained conjunction should verify independently");
}

#[test]
fn post_execution_simp_uses_the_introduced_antecedent_for_contradiction() {
    let c_source = r#"
        int32 branch_value(int32 x) {
            if (x != 0) {
                return 0;
            }
            return 1;
        }
    "#;
    let click_source = r#"
        verifying "branch.c";

        int32 branch_value(int32 x) {
            ensures x == 0 implies result == 1;
        } by {
            execute();
            simp();
        }
    "#;
    let sources = [("branch.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the vacuous path implication should close through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp legacy exit planning"
                    || name == "outcome simp compatibility construction"
        )),
        "introduced contradiction closure must bypass outcome compatibility planning: {events:#?}"
    );

    let expanded =
        expand_c0_claim_source(click_source, &sources, "branch_value", CProofClaim::Grouped)
            .expect("the retained introduced contradiction should expand");
    assert!(expanded.contains("intro();"), "{expanded}");
    assert!(expanded.contains("contradiction("), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the introduced contradiction should replay independently");
}

#[test]
fn post_execution_smart_have_builds_recursive_conjunction_on_proof() {
    let c_source = r#"
        int32 first(int32 x, int32 y) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "first.c";

        int32 first(int32 x, int32 y) {
            requires 1 <= x;
            requires 1 <= y;
            ensures 0 <= x and 0 <= y;
        } by {
            execute();
            have 0 <= x and 0 <= y by simp;
            assumption();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("first.c", c_source)])
    });
    verified.expect("the smart have should retain its recursively checked conjunction");
    let source_verification_events = events.iter().take_while(|event| {
        !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "whole-contract certificate construction"
        )
    });
    assert!(
        source_verification_events
            .into_iter()
            .all(|event| !matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name.starts_with("post-execution simple have replay")
                        || name == "post-execution smart have compatibility construction"
            )),
        "the checked smart have must not construct or replay a second proof: {events:#?}"
    );

    let have_offset = click_source
        .find("have 0 <= x and 0 <= y")
        .expect("proof should contain the selected smart have");
    let position = expansion::position_at_offset(click_source, have_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("first.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained smart have should expand");
    assert!(!expanded.contains("by simp"), "{expanded}");
    assert_eq!(
        expanded
            .matches("apply(int32_positive_is_nonnegative(")
            .count(),
        2,
        "{expanded}"
    );
    assert!(expanded.contains("split();"), "{expanded}");
    verify_c0_sources(&expanded, &[("first.c", c_source)])
        .expect("the retained smart have should verify independently");
}

#[test]
fn post_execution_existential_simp_retains_its_checked_scope() {
    let c_source = r#"
        int32 identity(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "identity.c";

        int32 identity(int32 x) {
            ensures exists (j: int32) { j == result } by {
                execute();
                witness(j = result);
                simp();
            }
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("exit witness should refine its checked obligation scope");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.ensures_0" && name == "surface certificate replay"
        )),
        "exit witness refinement must retain the accepted Proof path: {events:#?}"
    );

    let simp_offset = click_source
        .find("simp();")
        .expect("proof should contain the selected existential simp");
    let position = expansion::position_at_offset(click_source, simp_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("identity.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the checked existential obligation should expand");
    assert!(expanded.contains("witness(j = result);"), "{expanded}");
    assert!(expanded.contains("normalize();"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the retained witness/normalize scope should verify independently");
}

#[test]
fn bounded_range_witness_closes_on_the_checked_outcome_scope() {
    let c_source = r#"
        int32 witness_zero(int32 n) {
            return 0;
        }
    "#;
    let click_source = r#"
        verifying "witness.c";

        int32 witness_zero(int32 n) {
            requires 0 < n;
            ensures found_zero: (0..n).any(|k| { k == result }) by {
                execute();
                witness(k = 0);
                simp();
            }
        }
    "#;
    let sources = [("witness.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the bounded witness body should close through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp legacy exit planning"
                    || name == "outcome simp compatibility construction"
        )),
        "the checked bounded witness must not enter legacy outcome planning"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &sources,
        "witness_zero",
        CProofClaim::Ensure(0),
    )
    .expect("the retained bounded witness should expand");
    assert!(expanded.contains("witness(k = 0);"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the retained bounded witness should replay independently");
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("post-execution smart apply should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "surface certificate replay"
        )),
        "the post-execution smart apply must retain its checked Proof: {events:#?}"
    );

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

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the smart marked transport should verify before expansion");
    let simple_transport_checks = events
        .iter()
        .filter(|event| {
            matches!(
                event,
                crate::instrumentation::VerificationEvent::TacticStarted(tactic)
                    if tactic.claim == "pipeline.contract"
                        && tactic.tactic_name == "transport"
                        && tactic.class == "simple"
            )
        })
        .count();
    assert_eq!(
        simple_transport_checks, 1,
        "ordinary verification should not replay the smart transport before whole-certificate checking"
    );
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
        expanded.contains("if at(statement(0).entry, flag) != at(statement(0).entry, 0) {"),
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
        expanded.contains("if at(statement(0).entry, flag) != at(statement(0).entry, 0) {"),
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
fn pure_structural_simp_builds_recursive_conjunction_on_proof() {
    let click_source = r#"
        theorem nonnegative_pair_direct(x: int32, y: int32) {
            requires 1 <= x;
            requires 1 <= y;
            ensures 0 <= x and 0 <= y by simp;
        }

        theorem nonnegative_pair_script(x: int32, y: int32) {
            requires 1 <= x;
            requires 1 <= y;
            ensures 0 <= x and 0 <= y by {
                simp();
            }
        }

        theorem nonnegative_pair_branches(flag: int32, x: int32, y: int32) {
            requires 1 <= x;
            requires 1 <= y;
            ensures 0 <= x and 0 <= y by {
                if flag == 0 {
                    simp();
                } else {
                    simp();
                }
            }
        }
    "#;

    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("pure structural simp should retain both recursively checked child proofs");
    for claim in [
        "nonnegative_pair_direct.ensures_0",
        "nonnegative_pair_script.ensures_0",
        "nonnegative_pair_branches.ensures_0",
    ] {
        assert!(
            events.iter().all(|event| !matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished {
                    claim: event_claim,
                    name,
                    ..
                } if event_claim == claim && name == "surface certificate replay"
            )),
            "{claim} must retain its structural Proof descendant: {events:#?}"
        );
    }

    let script_start = click_source
        .find("theorem nonnegative_pair_script")
        .expect("the script theorem should be present");
    let branch_start = click_source
        .find("theorem nonnegative_pair_branches")
        .expect("the branch theorem should be present");
    for (offset, expected_applications) in [
        (
            click_source
                .find("simp;")
                .expect("the direct theorem should contain smart simp"),
            2,
        ),
        (
            script_start
                + click_source[script_start..]
                    .find("simp();")
                    .expect("the script theorem should contain smart simp"),
            2,
        ),
        (
            branch_start
                + click_source[branch_start..]
                    .find("simp();")
                    .expect("the branch theorem should contain smart simp"),
            4,
        ),
    ] {
        let position = expansion::position_at_offset(click_source, offset);
        let expanded =
            expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
                .expect("the retained pure conjunction should expand");
        assert_eq!(
            expanded
                .matches("apply(int32_positive_is_nonnegative(")
                .count(),
            expected_applications,
            "{expanded}"
        );
        assert!(expanded.contains("split();"), "{expanded}");
        verify_click_theorems(&expanded)
            .expect("the retained pure conjunction should verify independently");
    }
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("restricted equality simp should build its typed path through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "equality_transitive.ensures_0"
                    && name == "surface certificate replay"
        )),
        "restricted equality simp must retain its checked Proof descendant: {events:#?}"
    );
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
    assert!(expanded.contains("rewrite(y == z);"), "{expanded}");
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[]).expect("explicit equality certificate should replay");
}

#[test]
fn pure_rewrite_retains_a_structural_surface_successor_for_simp() {
    let click_source = r#"
        theorem rewrite_pair(x: int32, y: int32, z: int32) {
            requires x == y;
            requires y == 0;
            requires z == 0;
            ensures x <= 0 and z <= 0 by {
                rewrite(x == y);
                simp();
            }
        }
    "#;

    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("rewrite followed by structural simp should remain on Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "rewrite_pair.ensures_0" && name == "surface certificate replay"
        )),
        "the rewrite successor must not reconstruct and replay a second proof: {events:#?}"
    );

    let simp_offset = click_source
        .find("simp();")
        .expect("source should contain the structural smart step");
    let position = expansion::position_at_offset(click_source, simp_offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("the retained rewrite successor should expand");
    assert_eq!(expanded.matches("rewrite(").count(), 3, "{expanded}");
    assert!(expanded.contains("split();"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_click_theorems(&expanded)
        .expect("the expanded rewrite and structural child proofs should verify independently");
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

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("increment.c", c_source)])
    });
    verified.expect("the typed strict-increment rule should verify through the point Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment.contract"
                    && (name == "surface certificate replay"
                        || name == "derivation lowering: ambient rewrite harvest")
        )),
        "the retained strict-increment rule must not enter legacy certificate search: {events:#?}"
    );
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

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("increment.c", c_source)], line, column)
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
fn post_execution_simp_expands_increment_definedness() {
    let c_source = r#"
        int32 increment(int32 x) {
            return x + 1;
        }
    "#;
    let click_source = r#"
        verifying "increment.c";

        int32 increment(int32 x) {
            requires 2147483647 > x;
            ensures defined(x + 1);
        } by {
            execute();
            simp();
        }
    "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("increment.c", c_source)])
    });
    verified.expect("the typed increment-definedness rule should verify through the point Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment.contract"
                    && (name == "surface certificate replay"
                        || name == "derivation lowering: ambient rewrite harvest")
        )),
        "the retained increment-definedness rule must not enter legacy certificate search: {events:#?}"
    );
    let offset = click_source.rfind("simp()").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("increment.c", c_source)],
        position.line,
        position.column,
    )
    .expect("post-execution increment-definedness proof should expand");
    assert!(
        expanded.contains("apply(int32_increment_below_max_is_defined("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("increment.c", c_source)])
        .expect("expanded increment-definedness proof should replay");
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("increment_nonnegative.c", c_source)])
    });
    verified.expect("the typed increment-lower-bound rule should verify through the point Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_nonnegative.contract"
                    && (name == "surface certificate replay"
                        || name == "derivation lowering: ambient rewrite harvest")
        )),
        "the retained increment-lower-bound rule must not enter legacy certificate search: {events:#?}"
    );
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
fn restricted_simp_expands_nonstrict_unequal_order() {
    let click_source = r#"
        theorem nonstrict_unequal_is_strict(left: int32, right: int32) {
            requires left <= right;
            requires not (left == right);
            ensures left < right by {
                simp();
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("nonstrict unequal order should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "nonstrict_unequal_is_strict.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the named <=/!= strict-order step must not use construction replay: {events:#?}"
    );
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

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("nonstrict unequal order should expand");
    assert!(
        expanded.contains("apply(int32_le_and_neq_implies_lt(left, right)) using"),
        "{expanded}"
    );
    assert!(!expanded.contains("simp()"), "{expanded}");
    verify_click_theorems(&expanded).expect("nonstrict unequal certificate should replay");
}

#[test]
fn post_execution_simp_expands_increment_upper_bound() {
    let c_source = r#"
        int32 increment_below(int32 x) {
            return x + 1;
        }
    "#;
    let click_source = r#"
        verifying "increment_below.c";

        int32 increment_below(int32 x) {
            requires x < 10;
            ensures result <= 10;
        } by {
            execute();
            simp();
        }
    "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("increment_below.c", c_source)])
    });
    verified.expect("the typed increment bound should verify through the point Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_below.contract"
                    && (name == "surface certificate replay"
                        || name == "derivation lowering: ambient rewrite harvest")
        )),
        "the retained increment rule must not enter legacy certificate search: {events:#?}"
    );
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
        &[("increment_below.c", c_source)],
        line,
        column,
    )
    .expect("post-execution increment upper bound should expand");
    assert!(
        expanded.contains("apply(int32_increment_upper_bound("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("increment_below.c", c_source)])
        .expect("expanded increment upper-bound proof should replay");
}

#[test]
fn post_execution_simp_expands_strict_transitivity() {
    let c_source = r#"
        int32 return_first(int32 first, int32 middle, int32 last) {
            return first;
        }
    "#;
    let click_source = r#"
        verifying "return_first.c";

        int32 return_first(int32 first, int32 middle, int32 last) {
            requires first < middle;
            requires middle < last;
            ensures result < last;
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

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("return_first.c", c_source)], line, column)
            .expect("post-execution strict transitivity should expand");
    assert!(
        expanded.contains("apply(int32_lt_transitive("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("return_first.c", c_source)])
        .expect("expanded strict-transitivity proof should replay");
}

#[test]
fn post_execution_simp_expands_greater_equal_transitivity() {
    let c_source = r#"
        int32 return_last(int32 first, int32 middle, int32 last) {
            return last;
        }
    "#;
    let click_source = r#"
        verifying "return_last.c";

        int32 return_last(int32 first, int32 middle, int32 last) {
            requires first <= middle;
            requires middle <= last;
            ensures result >= first;
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

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("return_last.c", c_source)], line, column)
            .expect("post-execution non-strict transitivity should expand");
    assert!(
        expanded.contains("apply(int32_ge_transitive("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("return_last.c", c_source)])
        .expect("expanded non-strict-transitivity proof should replay");
}

#[test]
fn post_execution_simp_expands_greater_equal_increment_bound() {
    let c_source = r#"
        int32 increment_ge(int32 value) {
            return value + 1;
        }
    "#;
    let click_source = r#"
        verifying "increment_ge.c";

        int32 increment_ge(int32 value) {
            requires value >= 0;
            requires value < 2147483647;
            ensures result >= 0;
        } by {
            execute();
            simp();
        }
    "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("increment_ge.c", c_source)])
    });
    verified.expect("the typed greater-equal increment rule should verify through the point Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_ge.contract"
                    && (name == "surface certificate replay"
                        || name == "derivation lowering: ambient rewrite harvest")
        )),
        "the retained greater-equal increment rule must not enter legacy certificate search: {events:#?}"
    );
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

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("increment_ge.c", c_source)], line, column)
            .expect("post-execution greater-equal increment bound should expand");
    assert!(
        expanded.contains("apply(int32_increment_greater_equal_lower_bound("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("increment_ge.c", c_source)])
        .expect("expanded greater-equal increment proof should replay");
}

#[test]
fn post_execution_simp_expands_strict_greater_increment_bound() {
    let c_source = r#"
        int32 increment_gt(int32 value) {
            return value + 1;
        }
    "#;
    let click_source = r#"
        verifying "increment_gt.c";

        int32 increment_gt(int32 value) {
            requires value >= 0;
            requires value < 2147483647;
            ensures result > 0;
        } by {
            execute();
            simp();
        }
    "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("increment_gt.c", c_source)])
    });
    verified
        .expect("the typed strict-greater increment rule should verify through the point Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_gt.contract"
                    && (name == "surface certificate replay"
                        || name == "derivation lowering: ambient rewrite harvest")
        )),
        "the retained strict-greater increment rule must not enter legacy certificate search: {events:#?}"
    );
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

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("increment_gt.c", c_source)], line, column)
            .expect("post-execution strict-greater increment bound should expand");
    assert!(
        expanded.contains("apply(int32_increment_strict_greater_lower_bound("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("increment_gt.c", c_source)])
        .expect("expanded strict-greater increment proof should replay");
}

#[test]
fn post_execution_simp_expands_greater_order_equality() {
    let c_source = r#"
        int32 identity_zero(int32 value) {
            return value;
        }
    "#;
    let click_source = r#"
        verifying "identity_zero.c";

        int32 identity_zero(int32 value) {
            requires value >= 0;
            requires not (value > 0);
            ensures result == 0;
        } by {
            execute();
            simp();
        }
    "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity_zero.c", c_source)])
    });
    verified.expect("post-execution >=/not-> equality should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity_zero.ensures_0" && name == "surface certificate replay"
        )),
        "the outcome equality theorem must not use construction replay: {events:#?}"
    );

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

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity_zero.c", c_source)], line, column)
            .expect("post-execution greater-order equality should expand");
    assert!(
        expanded.contains("apply(int32_ge_and_not_gt_implies_eq("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity_zero.c", c_source)])
        .expect("expanded greater-order equality should replay");
}

#[test]
fn post_execution_simp_composes_negated_successor_bound() {
    let c_source = r#"
        int32 identity_at_least_one(int32 value) {
            return value;
        }
    "#;
    let click_source = r#"
        verifying "identity_at_least_one.c";

        int32 identity_at_least_one(int32 value) {
            requires not (value < 2);
            ensures result >= 1;
        } by {
            execute();
            simp();
        }
    "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity_at_least_one.c", c_source)])
    });
    verified.expect("the typed successor-bound Proof should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity_at_least_one.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the retained successor-bound proof must not use construction replay: {events:#?}"
    );
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
        &[("identity_at_least_one.c", c_source)],
        line,
        column,
    )
    .expect("post-execution successor lower bound should expand");
    assert!(
        expanded.contains("apply(int32_not_lt_implies_ge("),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_ge_transitive("),
        "{expanded}"
    );
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity_at_least_one.c", c_source)])
        .expect("expanded successor lower-bound proof should replay");
}

#[test]
fn restricted_simp_composes_negated_successor_bound() {
    let click_source = r#"
        theorem not_below_two_is_at_least_one(value: int32) {
            requires not (value < 2);
            ensures value >= 1 by {
                simp() using {
                    not (value < 2);
                }
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the restricted successor-bound Proof should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "not_below_two_is_at_least_one.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the retained restricted successor-bound proof must not use construction replay: {events:#?}"
    );
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
        .expect("restricted successor lower bound should expand");
    assert!(
        expanded.contains("apply(int32_not_lt_implies_ge("),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_ge_transitive("),
        "{expanded}"
    );
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded restricted successor proof should replay");
}

#[test]
fn post_execution_simp_unfolds_predicate_goal_explicitly() {
    let c_source = r#"
        int32 compare_swap2(int32* p) {
            int32 tmp;
            if (p[1] < p[0]) {
                tmp = p[0];
                p[0] = p[1];
                p[1] = tmp;
            } else {
                tmp = 0;
            }
            return 0;
        }
    "#;
    let click_source = r#"
        verifying "compare_swap2.c";

        predicate sorted_pair(p: int32*) {
            p[0] <= p[1]
        }

        int32 compare_swap2(int32* p) {
            requires loadable(p[0..2]);
            consumes p[0..2];
            ensures sorted_pair(p);
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

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("compare_swap2.c", c_source)], line, column)
            .expect("post-execution predicate goal should expand");
    assert!(expanded.contains("unfold(sorted_pair);"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("compare_swap2.c", c_source)])
        .expect("expanded predicate-goal proof should replay");
}

#[test]
fn pure_simp_retains_one_selected_equality_rewrite_before_normalize() {
    let click_source = r#"
        theorem predecessor_of_one_is_nonnegative(value: int32) {
            requires value == 1;

            ensures 0 <= value - 1 by {
                simp();
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the selected equality rewrite should close on the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "predecessor_of_one_is_nonnegative.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the selected rewrite path must not use construction replay: {events:#?}"
    );

    let offset = click_source.find("simp()").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("the retained equality-refinement path should expand");
    assert!(expanded.contains("rewrite(value == 1);"), "{expanded}");
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_click_theorems(&expanded).expect("the expanded rewrite path should replay");
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed increment rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_stays_bounded.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the retained pure increment rule must not use construction replay: {events:#?}"
    );
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("positive-to-nonnegative simp should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "positive_is_nonnegative.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the named positive-to-nonnegative step must not use construction replay: {events:#?}"
    );
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
fn restricted_simp_expands_strictly_positive_to_nonnegative_theorem_application() {
    let click_source = r#"
        theorem strictly_positive_is_nonnegative(value: int32) {
            requires 0 < value;
            ensures value >= 0 by {
                simp() using {
                    0 < value;
                }
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("strictly-positive-to-nonnegative simp should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "strictly_positive_is_nonnegative.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the named strictly-positive-to-nonnegative step must not use construction replay: {events:#?}"
    );
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
        .expect("strictly-positive-to-nonnegative simp should expand");
    assert!(
        expanded.contains("apply(int32_strictly_positive_is_nonnegative(value)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("0 < value;"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed predecessor-nonnegative rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "positive_predecessor_is_nonnegative.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the retained predecessor-nonnegative rule must not use construction replay: {events:#?}"
    );
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed predecessor-decrease rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "positive_predecessor_decreases.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the retained predecessor-decrease rule must not use construction replay: {events:#?}"
    );
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
        expanded.contains("apply(int32_positive_predecessor_strictly_decreases(value)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("0 < value;"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should replay");
}

#[test]
fn restricted_simp_expands_predecessor_upper_bound_to_theorem_application() {
    let click_source = r#"
        theorem predecessor_keeps_upper_bound(value: int32, bound: int32) {
            requires 0 <= value;
            requires value <= bound;
            ensures value - 1 <= bound by {
                simp() using {
                    0 <= value;
                    value <= bound;
                }
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed predecessor-upper-bound rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "predecessor_keeps_upper_bound.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the retained predecessor-upper-bound rule must not use construction replay: {events:#?}"
    );
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("predecessor upper-bound simp should expand");
    assert!(
        expanded.contains("apply(int32_nonnegative_predecessor_upper_bound(value, bound)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("0 <= value;"), "{expanded}");
    assert!(expanded.contains("value <= bound;"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded predecessor theorem should replay");
}

#[test]
fn restricted_simp_retains_nested_one_le_predecessor_nonnegative_proof() {
    let click_source = r#"
        theorem one_le_predecessor_is_nonnegative(value: int32) {
            requires 1 <= value;
            ensures 0 <= value - 1 by {
                simp() using {
                    1 <= value;
                }
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the nested predecessor proof should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "one_le_predecessor_is_nonnegative.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the retained nested predecessor proof must not use construction replay: {events:#?}"
    );
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("one-le predecessor proof should expand");
    assert!(expanded.contains("have 0 < value"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_successor_le_implies_lt(0, value)) using"),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_positive_predecessor_is_nonnegative(value)) using"),
        "{expanded}"
    );
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded nested predecessor proof should replay");
}

#[test]
fn restricted_simp_retains_nested_one_le_predecessor_decrease_proof() {
    let click_source = r#"
        theorem one_le_predecessor_decreases(value: int32) {
            requires 1 <= value;
            ensures value - 1 < value by {
                simp() using {
                    1 <= value;
                }
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the nested predecessor-decrease proof should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "one_le_predecessor_decreases.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the retained nested predecessor-decrease proof must not use construction replay: {events:#?}"
    );
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("one-le predecessor-decrease proof should expand");
    assert!(expanded.contains("have 0 < value"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_successor_le_implies_lt(0, value)) using"),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_positive_predecessor_strictly_decreases(value)) using"),
        "{expanded}"
    );
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded)
        .expect("expanded nested predecessor-decrease proof should replay");
}

#[test]
fn restricted_simp_retains_equal_one_predecessor_path() {
    let click_source = r#"
        theorem equal_one_predecessor_is_nonnegative(value: int32) {
            requires 1 == value;
            ensures 0 <= value - 1 by {
                simp() using {
                    1 == value;
                }
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the equal-one predecessor proof should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "equal_one_predecessor_is_nonnegative.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the retained equal-one path must not use construction replay: {events:#?}"
    );
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("equal-one predecessor proof should expand");
    assert!(expanded.contains("have 1 <= value"), "{expanded}");
    assert!(expanded.contains("rewrite(value == 1)"), "{expanded}");
    assert!(expanded.contains("have 0 < value"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_positive_predecessor_is_nonnegative(value)) using"),
        "{expanded}"
    );
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded equal-one predecessor proof should replay");
}

#[test]
fn restricted_simp_retains_equal_one_predecessor_zero_path() {
    let click_source = r#"
        theorem equal_one_predecessor_is_zero(value: int32) {
            requires 1 == value;
            ensures value - 1 == 0 by {
                simp() using {
                    1 == value;
                }
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the predecessor-zero proof should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "equal_one_predecessor_is_zero.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the retained predecessor-zero path must not use construction replay: {events:#?}"
    );
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("equal-one predecessor-zero proof should expand");
    assert!(expanded.contains("rewrite(value == 1)"), "{expanded}");
    assert!(expanded.contains("normalize()"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded predecessor-zero proof should replay");
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed strict-increment rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_is_greater.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the retained pure strict-increment rule must not use construction replay: {events:#?}"
    );
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
fn simp_expands_increment_definedness_to_theorem_application() {
    let click_source = r#"
        theorem increment_is_defined(value: int32) {
            requires value < 2147483647;
            ensures defined(value + 1) by {
                simp();
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed increment-definedness rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_is_defined.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the retained pure increment-definedness rule must not use construction replay: {events:#?}"
    );
    let offset = click_source.find("simp()").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("increment-definedness simp should expand");
    assert!(
        expanded.contains("apply(int32_increment_below_max_is_defined(value)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("value < 2147483647;"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded increment-definedness proof should replay");
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed increment-lower-bound rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_preserves_lower_bound.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the retained pure increment-lower-bound rule must not use construction replay: {events:#?}"
    );
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed increment-order rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_preserves_order.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the retained increment-order rule must not use construction replay: {events:#?}"
    );
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
fn restricted_simp_rewrites_a_named_successor_before_increment_order() {
    let c_source = r#"
        int32 named_successor(int32 value) {
            int32 successor;
            successor = value + 1;
            return successor;
        }
    "#;
    let click_source = r#"
        verifying "named_successor.c";

        int32 named_successor(int32 value) {
            requires 0 <= value;
            requires value < 2147483647;
            ensures 1 <= result by {
                execute();
                simp();
            }
        }
    "#;
    let offset = click_source.find("simp()").unwrap();
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
        &[("named_successor.c", c_source)],
        line,
        column,
    )
    .expect("named successor order should lower to an explicit rewrite and increment rule");
    assert!(
        expanded.contains("apply(int32_increment_preserves_order("),
        "{expanded}"
    );
    assert!(
        expanded.contains("at(statement(1).entry, value)"),
        "{expanded}"
    );
    assert!(!expanded.contains("simp()"), "{expanded}");
    verify_c0_sources(&expanded, &[("named_successor.c", c_source)])
        .expect("named successor certificate should replay");
}

#[test]
fn restricted_simp_certifies_unchanged_prefix_after_indexed_store() {
    let c_source = r#"
        struct vector {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 vector_push(struct vector* owner, int32 value) {
            int32 index;
            int32* data;
            index = owner->len;
            data = owner->data;
            data[index] = value;
            owner->len = index + 1;
            return owner->len;
        }
    "#;
    let click_source = r#"
        resource vector_storage(owner: struct vector*) {
            owns owner->len;
            owns owner->cap;
            owns owner->data;
            owns owner->data[0..owner->cap];
            fact 0 <= owner->len;
            fact owner->len <= owner->cap;
            fact loadable(owner->data[0..owner->len]);
            fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        }

        verifying "vector_push.c";

        int32 vector_push(struct vector* owner, int32 value) {
            requires owner->len < owner->cap;
            owns vector_storage(owner);
            mutable owner->len, owner->data[owner->len..owner->len + 1];
            ensures result == old(owner->len) + 1;
            ensures owner->len == old(owner->len) + 1;
            ensures owner->data[old(owner->len)] == value;
            ensures owner->cap == old(owner->cap);
            ensures owner->data == old(owner->data);
            ensures forall (k: int32) {
                0 <= k and k < old(owner->len) implies
                    owner->data[k] == old(owner->data[k])
            };
        } by {
            unfold(vector_storage(owner));
            execute();
            fold(vector_storage(owner));
            frame();
            simp();
        }
    "#;
    let offset = click_source.rfind("simp();").unwrap();
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
        expand_c0_tactic_source_at(click_source, &[("vector_push.c", c_source)], line, column)
            .expect("unchanged-prefix simp should expand to a replayable frame transport");
    assert!(
        expanded.contains("transport(old(owner->data[k])"),
        "{expanded}"
    );
    assert!(expanded.contains("k < old(owner->len)"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_c0_sources(&expanded, &[("vector_push.c", c_source)])
        .expect("unchanged-prefix certificate should replay");
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed adjacent-order rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "two_at_most_implies_one_below.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the retained adjacent-order proof must not use construction replay: {events:#?}"
    );
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
fn smart_simp_transcribes_a_three_edge_signed_order_path() {
    let click_source = r#"
        theorem three_edge_order_chain(
            first: int32,
            second: int32,
            third: int32,
            last: int32
        ) {
            requires first <= second;
            requires second < third;
            requires third <= last;
            ensures first < last by {
                simp();
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the checked order-path Proof should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "three_edge_order_chain.ensures_0"
                    && name == "surface certificate replay"
        )),
        "signed-order simp should construct its Proof through checked theorem applications: {events:#?}"
    );
    let offset = click_source.find("simp();").unwrap();
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
        .expect("the retained three-edge order path should expand");
    assert!(
        expanded.contains("apply(int32_le_lt_transitive(first, second, third)) using"),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_lt_le_transitive(first, third, last)) using"),
        "{expanded}"
    );
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_click_theorems(&expanded).expect("the transcribed order path should replay");
}

#[test]
fn smart_simp_transcribes_a_three_edge_bitvector_equality_path() {
    let click_source = r#"
        theorem three_edge_equality_chain(
            first: int32,
            second: int32,
            third: int32,
            last: int32
        ) {
            requires second == first;
            requires second == third;
            requires third == last;
            ensures first == last by {
                simp();
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the checked equality-path Proof should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "three_edge_equality_chain.ensures_0"
                    && name == "surface certificate replay"
        )),
        "equality simp should construct its Proof through checked rewrites: {events:#?}"
    );

    let offset = click_source.find("simp();").unwrap();
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
        .expect("the retained three-edge equality path should expand");
    assert!(expanded.contains("rewrite(first == second);"), "{expanded}");
    assert!(expanded.contains("rewrite(second == third);"), "{expanded}");
    assert!(expanded.contains("rewrite(third == last);"), "{expanded}");
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_click_theorems(&expanded).expect("the transcribed equality path should replay");
}

#[test]
fn smart_simp_retains_both_signed_equality_rules_as_named_steps() {
    let click_source = r#"
        theorem le_and_not_lt_are_equal(left: int32, right: int32) {
            requires left <= right;
            requires not (left < right);
            ensures left == right by {
                simp();
            }
        }

        theorem ge_and_not_gt_are_equal(left: int32, right: int32) {
            requires left >= right;
            requires not (left > right);
            ensures left == right by {
                simp();
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed <=/not-< equality rule should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if (claim == "le_and_not_lt_are_equal.ensures_0"
                    || claim == "ge_and_not_gt_are_equal.ensures_0")
                    && name == "surface certificate replay"
        )),
        "the named equality step must not use construction replay: {events:#?}"
    );

    let offset = click_source.find("simp();").unwrap();
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
        .expect("the retained equality theorem should expand");
    assert!(
        expanded.contains("apply(int32_le_and_not_lt_implies_eq(left, right)) using"),
        "{expanded}"
    );
    verify_click_theorems(&expanded).expect("the named equality step should independently replay");

    let offset = click_source.rfind("simp();").unwrap();
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
        .expect("the retained >=/not-> equality theorem should expand");
    assert!(
        expanded.contains("apply(int32_ge_and_not_gt_implies_eq(left, right)) using"),
        "{expanded}"
    );
    verify_click_theorems(&expanded)
        .expect("the named >=/not-> equality step should independently replay");
}

#[test]
fn outcome_simp_consumes_its_recorded_bitvector_equality_path() {
    let c_source = r#"
        int32 choose_first(int32 first, int32 second, int32 third, int32 last) {
            return first;
        }
    "#;
    let click_source = r#"
        verifying "choose_first.c";

        int32 choose_first(int32 first, int32 second, int32 third, int32 last) {
            requires second == first;
            requires second == third;
            requires third == last;
            ensures result == last;
        } by {
            execute();
            simp();
        }
    "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("choose_first.c", c_source)])
    });
    verified.expect("the outcome equality path should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "choose_first.contract"
                    && name == "derivation lowering: ambient rewrite harvest"
        )),
        "the typed outcome path must not scan ambient equalities: {events:#?}"
    );

    let offset = click_source.rfind("simp();").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("choose_first.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained outcome equality path should expand");
    assert!(
        expanded.contains("rewrite(at(function.entry, first == second));"),
        "{expanded}"
    );
    assert!(
        expanded.contains("rewrite(at(function.entry, second == third));"),
        "{expanded}"
    );
    assert!(
        expanded.contains("rewrite(at(function.entry, third == last));"),
        "{expanded}"
    );
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_c0_sources(&expanded, &[("choose_first.c", c_source)])
        .expect("the transcribed outcome equality path should replay");
}

#[test]
fn outcome_simp_applies_theorems_through_its_recorded_order_path() {
    let c_source = r#"
        int32 validate_chain(int32 first, int32 second, int32 third, int32 last) {
            return first;
        }
    "#;
    let click_source = r#"
        verifying "validate_chain.c";

        int32 validate_chain(int32 first, int32 second, int32 third, int32 last) {
            requires first <= second;
            requires second < third;
            requires third <= last;
            ensures first < last;
        } by {
            execute();
            simp();
        }
    "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("validate_chain.c", c_source)])
    });
    verified.expect("the outcome order path should verify through the point Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "validate_chain.contract"
                    && name == "surface certificate replay"
        )),
        "the outcome theorem path must retain its checked Proof successor: {events:#?}"
    );

    let offset = click_source.rfind("simp();").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("validate_chain.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained outcome theorem path should expand");
    assert!(
        expanded.contains(
            "apply(int32_le_lt_transitive(at(function.entry, first), at(function.entry, second), at(function.entry, third))) using"
        ),
        "{expanded}"
    );
    assert!(
        expanded.contains(
            "apply(int32_lt_le_transitive(at(function.entry, first), at(function.entry, third), at(function.entry, last))) using"
        ),
        "{expanded}"
    );
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_c0_sources(&expanded, &[("validate_chain.c", c_source)])
        .expect("the transcribed outcome theorem path should replay");
}

#[test]
fn restricted_simp_expands_constant_order_weakening_to_theorem_application() {
    let click_source = r#"
        theorem three_at_least_implies_nonnegative(value: int32) {
            requires 3 <= value;
            ensures 0 <= value by {
                simp() using {
                    3 <= value;
                }
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the constant lower-bound weakening should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "three_at_least_implies_nonnegative.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the constant lower-bound proof should retain its checked Proof successor: {events:#?}"
    );
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
        .expect("constant order weakening simp should expand");
    assert!(
        expanded.contains("apply(int32_le_transitive(0, 3, value)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("3 <= value;"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should replay");
}

#[test]
fn restricted_simp_expands_constant_strict_upper_bound_to_theorem_application() {
    let click_source = r#"
        theorem three_at_most_implies_below_five(value: int32) {
            requires value <= 3;
            ensures value < 5 by {
                simp() using {
                    value <= 3;
                }
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the constant strict upper-bound weakening should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "three_at_most_implies_below_five.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the constant upper-bound proof should retain its checked Proof successor: {events:#?}"
    );
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("constant strict upper-bound simp should expand");
    assert!(
        expanded.contains("apply(int32_le_lt_transitive(value, 3, 5)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("value <= 3;"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded strict upper-bound proof should replay");
}

#[test]
fn restricted_simp_retains_increment_under_a_larger_constant() {
    let click_source = r#"
        theorem increment_three_at_most_is_five_at_most(value: int32) {
            requires value <= 3;
            ensures value + 1 <= 5 by {
                simp() using {
                    value <= 3;
                }
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the increment constant-bound rule should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_three_at_most_is_five_at_most.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the increment constant-bound proof must retain both checked theorem steps: {events:#?}"
    );
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("increment constant-bound simp should expand");
    assert!(
        expanded.contains("apply(int32_le_lt_transitive(value, 3, 5)) using"),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_increment_upper_bound(value, 5)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("value <= 3;"), "{expanded}");
    assert!(expanded.contains("value < 5;"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    verify_click_theorems(&expanded)
        .expect("expanded increment constant-bound proof should replay");
}

#[test]
fn restricted_simp_retains_symbolic_add_definedness_theorem() {
    let click_source = r#"
        theorem symbolic_add_is_defined(value: int32, amount: int32) {
            requires amount >= 0;
            requires 2147483647 - amount >= value;
            ensures defined(value + amount) by {
                simp() using {
                    amount >= 0;
                    2147483647 - amount >= value;
                }
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the symbolic-add definedness rule should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "symbolic_add_is_defined.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the symbolic-add proof must retain its checked theorem application: {events:#?}"
    );
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("symbolic-add definedness simp should expand");
    assert!(
        expanded
            .contains("apply(int32_nonnegative_add_within_max_is_defined(value, amount)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("amount >= 0;"), "{expanded}");
    assert!(
        expanded.contains("2147483647 - amount >= value;"),
        "{expanded}"
    );
    assert!(!expanded.contains("simp() using"), "{expanded}");
    verify_click_theorems(&expanded)
        .expect("expanded symbolic-add definedness proof should replay");
}

#[test]
fn restricted_simp_retains_symbolic_subtract_definedness_theorem() {
    let click_source = r#"
        theorem symbolic_subtract_is_defined(value: int32, amount: int32) {
            requires amount >= 0;
            requires value >= amount;
            ensures defined(value - amount) by {
                simp() using {
                    amount >= 0;
                    value >= amount;
                }
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the symbolic-subtract definedness rule should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "symbolic_subtract_is_defined.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the symbolic-subtract proof must retain its checked theorem application: {events:#?}"
    );
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("symbolic-subtract definedness simp should expand");
    assert!(
        expanded.contains(
            "apply(int32_nonnegative_subtract_within_value_is_defined(value, amount)) using"
        ),
        "{expanded}"
    );
    assert!(expanded.contains("amount >= 0;"), "{expanded}");
    assert!(expanded.contains("value >= amount;"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    verify_click_theorems(&expanded)
        .expect("expanded symbolic-subtract definedness proof should replay");
}

#[test]
fn restricted_simp_retains_one_plus_operand_specific_theorems() {
    let cases = [
        (
            r#"
                theorem one_plus_is_defined(value: int32) {
                    requires 2147483647 > value;
                    ensures defined(1 + value) by {
                        simp() using { 2147483647 > value; }
                    }
                }
            "#,
            "one_plus_is_defined.ensures_0",
            "apply(int32_one_plus_below_max_is_defined(value)) using",
        ),
        (
            r#"
                theorem one_plus_increases(value: int32) {
                    requires 2147483647 > value;
                    ensures value < 1 + value by {
                        simp() using { 2147483647 > value; }
                    }
                }
            "#,
            "one_plus_increases.ensures_0",
            "apply(int32_one_plus_strictly_increases(value)) using",
        ),
    ];
    for (click_source, claim, application) in cases {
        let (verified, events) =
            crate::instrumentation::collect(|| verify_click_theorems(click_source));
        verified.expect("the operand-order-specific one-plus rule should verify through Proof");
        assert!(
            events.iter().all(|event| !matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished {
                    claim: event_claim,
                    name,
                    ..
                } if event_claim == claim && name == "surface certificate replay"
            )),
            "the one-plus proof must retain its checked theorem application: {events:#?}"
        );
        let offset = click_source.find("simp() using").unwrap();
        let position = expansion::position_at_offset(click_source, offset);
        let expanded =
            expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
                .expect("one-plus simp should expand");
        assert!(expanded.contains(application), "{expanded}");
        assert!(expanded.contains("2147483647 > value;"), "{expanded}");
        assert!(!expanded.contains("simp() using"), "{expanded}");
        verify_click_theorems(&expanded).expect("expanded one-plus proof should replay");
    }
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
    assert!(expanded_have.contains("normalize();"), "{expanded_have}");
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
    let normalized_have = expanded_have
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>()
        .join("\n");
    assert_eq!(
        normalized_have,
        "have loadable(data[index..(index + 1)]) by {\n\
         transport(loadable(data[0..length]), loadable(data[index..(index + 1)])) using {\n\
         loadable(data[0..length]);\n\
         0 <= index;\n\
         index < length;\n\
         }\n\
         }"
    );
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
    let selected = &expanded[offset..];
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
fn point_have_bare_apply_retains_and_checks_its_exact_premise() {
    let c_source = r#"
            int32 choose_second(int32 first, int32 second) {
                return second;
            }
        "#;
    let click_source = r#"
            theorem equality_symmetric(first: int32, second: int32) {
                requires first == second;
                ensures second == first by {
                    simp() using { first == second; }
                }
            }

            verifying "choose.c";

            int32 choose_second(int32 first, int32 second) {
                requires first == second;
                ensures second == first;
            } by {
                have second == first by {
                    apply(equality_symmetric(first, second));
                }
                step();
                assumption();
            }
        "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("choose.c", c_source)])
    });
    verified.expect("checked point apply should verify without ordinary certificate replay");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "choose_second.contract" && name == "surface certificate replay"
        )),
        "the migrated smart point proof must not pass through the ordinary construction/replay gateway: {events:#?}"
    );
    let have_offset = click_source
        .find("have second == first")
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
            .expect("checked point apply should expand");
    let apply_offset = expanded
        .find("apply(equality_symmetric(first, second)) using {")
        .expect("expansion should retain the selected explicit step");
    let premise_relative = expanded[apply_offset..]
        .find("first == second;")
        .expect("explicit step should retain the theorem premise");
    let premise_offset = apply_offset + premise_relative;
    verify_c0_sources(&expanded, &[("choose.c", c_source)])
        .expect("the retained point proof should independently replay");

    let mut corrupted = expanded.clone();
    corrupted.replace_range(
        premise_offset..premise_offset + "first == second;".len(),
        "",
    );
    let error = verify_c0_sources(&corrupted, &[("choose.c", c_source)])
        .expect_err("omitting the selected premise must invalidate the explicit proof");
    assert!(
        error.message().contains("required exact fact")
            || error.message().contains("unavailable exact premise"),
        "unexpected corrupted-certificate error: {}",
        error.message()
    );
}

#[test]
fn point_have_mixed_linear_smart_script_continues_on_checked_successors() {
    let c_source = r#"
            int32 choose_second(int32 first, int32 second) {
                return second;
            }
        "#;
    let click_source = r#"
            theorem equality_symmetric(first: int32, second: int32) {
                requires first == second;
                ensures second == first by {
                    simp() using { first == second; }
                }
            }

            verifying "choose.c";

            int32 choose_second(int32 first, int32 second) {
                requires (first == second) and (first >= 0);
                ensures result == second;
            } by {
                have second == first and first == second by {
                    extract(first == second);
                    apply(equality_symmetric(first, second));
                    simp();
                }
                step();
                simp();
            }
        "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("choose.c", c_source)])
    });
    verified.expect("smart apply should continue from its checked Proof successor");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "choose_second.contract" && name == "surface certificate replay"
        )),
        "the migrated apply-then-simp proof must not use construction replay: {events:#?}"
    );

    let have_offset = click_source
        .find("have second == first and first == second")
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
            .expect("the retained apply-then-simp path should expand");
    let expanded_have = &expanded[expanded
        .find("have second == first and first == second")
        .or_else(|| expanded.find("have (second == first) and (first == second)"))
        .expect("expanded proof should retain the selected have")
        ..expanded
            .find("step()")
            .expect("expanded proof should retain its suffix")];
    assert!(
        expanded_have.contains("apply(equality_symmetric(first, second)) using {"),
        "{expanded_have}"
    );
    assert!(
        expanded_have.contains("extract(first == second);"),
        "{expanded_have}"
    );
    assert!(
        expanded_have.contains("normalize();") || expanded_have.contains("split();"),
        "{expanded_have}"
    );
    assert!(!expanded_have.contains("simp();"), "{expanded_have}");
    verify_c0_sources(&expanded, &[("choose.c", c_source)])
        .expect("the serialized retained proof should independently reverify");
}

#[test]
fn execution_bare_apply_selects_and_retains_its_step_through_proof() {
    let c_source = r#"
            int32 keep(int32 value, int32 upper) {
                return value;
            }
        "#;
    let click_source = r#"
            verifying "keep.c";

            int32 keep(int32 value, int32 upper) {
                requires value < upper;
                ensures result <= upper;
            } by {
                apply(int32_lt_implies_le(value, upper));
                step();
                assumption();
            }
        "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("keep.c", c_source)])
    });
    let verified = verified.expect("checked execution apply should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "keep.contract" && name == "surface certificate replay"
        )),
        "the migrated execution apply must not pass through ordinary certificate replay: {events:#?}"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the checked execution apply should retain an expansion");
    assert!(matches!(
        expanded.first(),
        Some(ProofTactic::ApplyTheoremUsing { application, premises })
            if application.name == "int32_lt_implies_le" && premises.len() == 1
    ));
    let retained_source = verified[0]
        .expanded_proof_source()
        .expect("the checked execution apply should have canonical source");
    assert!(retained_source.contains("apply(int32_lt_implies_le(value, upper)) using {"));
    let expanded = expand_c0_claim_source(
        click_source,
        &[("keep.c", c_source)],
        "keep",
        CProofClaim::Grouped,
    )
    .expect("the checked execution apply should expand into source");
    verify_c0_sources(&expanded, &[("keep.c", c_source)])
        .expect("the retained execution theorem step should independently reverify");
}

#[test]
fn execution_resource_unfold_is_recorded_once_and_replays() {
    let c_source = r#"
        int32 discard(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "discard.c";

        int32 discard(int32 x) {
            consumes marker(x);
            immutable;
            ensures result == x;
        } by {
            unfold(marker(x));
            execute();
            frame();
            assumption();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("discard.c", c_source)])
        .expect("the explicit resource unfold should verify through Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its simple expansion");
    assert_eq!(
        tactics
            .iter()
            .filter(|tactic| matches!(tactic, ProofTactic::UnfoldResource(_)))
            .count(),
        1,
        "one source unfold must produce exactly one retained step"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("discard.c", c_source)],
        "discard",
        CProofClaim::Grouped,
    )
    .expect("the grouped resource proof should expand");
    assert_eq!(expanded.matches("unfold(marker(x));").count(), 1);
    verify_c0_sources(&expanded, &[("discard.c", c_source)])
        .expect("the one retained unfold should independently replay");
}

#[test]
fn execution_resource_observe_is_recorded_once_and_replays() {
    let c_source = r#"
        int32 inspect(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "inspect.c";

        int32 inspect(int32 x) {
            views marker(x);
            immutable;
            ensures result == x;
        } by {
            observe(marker(x));
            execute();
            frame();
            assumption();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("inspect.c", c_source)])
        .expect("the explicit resource observation should verify through Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its simple expansion");
    assert_eq!(
        tactics
            .iter()
            .filter(|tactic| matches!(tactic, ProofTactic::ObserveResource(_)))
            .count(),
        1,
        "one source observation must produce exactly one retained step"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("inspect.c", c_source)],
        "inspect",
        CProofClaim::Grouped,
    )
    .expect("the grouped resource proof should expand");
    assert_eq!(expanded.matches("observe(marker(x));").count(), 1);
    verify_c0_sources(&expanded, &[("inspect.c", c_source)])
        .expect("the one retained observation should independently replay");
}

#[test]
fn execution_resource_fold_is_recorded_once_and_replays() {
    let c_source = r#"
        int32 preserve(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "preserve.c";

        int32 preserve(int32 x) {
            owns marker(x);
            immutable;
            ensures result == x;
        } by {
            unfold(marker(x));
            fold(marker(x));
            execute();
            frame();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("preserve.c", c_source)])
        .expect("the explicit resource fold should verify through Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its simple expansion");
    assert_eq!(
        tactics
            .iter()
            .filter(|tactic| matches!(tactic, ProofTactic::FoldResource(_)))
            .count(),
        1,
        "one source fold must produce exactly one retained step"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("preserve.c", c_source)],
        "preserve",
        CProofClaim::Grouped,
    )
    .expect("the grouped resource proof should expand");
    assert_eq!(
        expanded
            .lines()
            .filter(|line| line.trim() == "fold(marker(x));")
            .count(),
        1
    );
    verify_c0_sources(&expanded, &[("preserve.c", c_source)])
        .expect("the one retained fold should independently replay");
}

#[test]
fn linear_execution_open_retains_one_checked_scope_and_replays() {
    let c_source = r#"
        int32 two_steps(int32 x) {
            x = x;
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "two_steps.c";

        int32 two_steps(int32 x) {
            owns marker(x);
            immutable;
            ensures result == x;
        } by {
            open(marker(x)) {
                step();
            }
            step();
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("two_steps.c", c_source)])
    });
    let verified = verified.expect("the linear open scope should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "two_steps.contract" && name == "surface certificate replay"
        )),
        "ordinary linear open construction must retain its checked Proof scope: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its simple expansion");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(open.tactics.as_slice(), [ProofTactic::StepUsing(_)])
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("two_steps.c", c_source)],
        "two_steps",
        CProofClaim::Grouped,
    )
    .expect("the grouped open proof should expand");
    verify_c0_sources(&expanded, &[("two_steps.c", c_source)])
        .expect("the retained open scope should independently replay");
}

#[test]
fn linear_execute_inside_open_retains_checked_statement_steps() {
    let c_source = r#"
        int32 two_steps(int32 x) {
            x = x;
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "two_steps.c";

        int32 two_steps(int32 x) {
            owns marker(x);
            immutable;
            ensures result == x;
        } by {
            open(marker(x)) {
                execute();
            }
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("two_steps.c", c_source)])
    });
    let verified = verified.expect("linear execute should advance inside the open Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "two_steps.contract" && name == "surface certificate replay"
        )),
        "ordinary scoped execute must retain its checked statement steps: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its scoped execution");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [ProofTactic::StepUsing(_), ProofTactic::StepUsing(_)]
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("two_steps.c", c_source)],
        "two_steps",
        CProofClaim::Grouped,
    )
    .expect("the grouped scoped execute should expand");
    verify_c0_sources(&expanded, &[("two_steps.c", c_source)])
        .expect("the retained scoped statement steps should independently replay");
}

#[test]
fn explicit_frame_inside_open_closes_its_owned_effect_goal_once() {
    let c_source = r#"
        int32 two_steps(int32 x) {
            x = x;
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "two_steps.c";

        int32 two_steps(int32 x) {
            owns marker(x);
            immutable;
            ensures result == x;
        } by {
            open(marker(x)) {
                execute();
                frame() using {};
            }
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("two_steps.c", c_source)])
    });
    let verified = verified.expect("the explicit frame should close the open Proof's effect goal");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "two_steps.contract"
                    && matches!(name.as_str(), "surface certificate replay" | "frame exact effect check")
        )),
        "the retained frame must neither replay nor recheck its effect at finalization: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its frame step");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [
                        ProofTactic::StepUsing(_),
                        ProofTactic::StepUsing(_),
                        ProofTactic::FrameUsing { region: None, premises }
                    ] if premises.is_empty()
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("two_steps.c", c_source)],
        "two_steps",
        CProofClaim::Grouped,
    )
    .expect("the grouped checked frame should expand");
    verify_c0_sources(&expanded, &[("two_steps.c", c_source)])
        .expect("the retained explicit frame should independently replay");
}

#[test]
fn smart_immutable_frame_inside_open_selects_a_checked_simple_step() {
    let c_source = r#"
        int32 identity(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "identity.c";

        int32 identity(int32 x) {
            owns marker(x);
            immutable;
            ensures result == x;
        } by {
            open(marker(x)) {
                execute();
                frame();
            }
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    let verified = verified.expect("the smart frame should retain its checked simple successor");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract"
                    && matches!(name.as_str(), "surface certificate replay" | "frame exact effect check")
        )),
        "smart frame search must not replay or recheck its selected step: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the smart frame proof should expose its retained certificate");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [
                        ProofTactic::StepUsing(_),
                        ProofTactic::FrameUsing { region: None, premises }
                    ] if premises.is_empty()
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Grouped,
    )
    .expect("the smart immutable frame should expand");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the selected empty frame step should independently replay");
}

#[test]
fn mutable_frame_distinguishes_legacy_empty_source_from_smart_exact_candidate() {
    let c_source = r#"
        int32 increment(int32 p[]) {
            p[0] = p[0] + 1;
            return p[0];
        }
    "#;
    let click_source = r#"
        resource counted(p: int32*) {
            owns p[0..1];
            fact p[0] == count(counted(p));
        }

        verifying "increment.c";

        int32 increment(int32 p[]) {
            owns counted(p);
            produces counted(p);
            mutable p[0..1];
        } by {
            open(counted(p)) {
                execute();
                frame() using {};
            }
            simp();
        }
    "#;

    verify_c0_sources(click_source, &[("increment.c", c_source)])
        .expect("an empty mutable frame must fall back to ambient-fact selection");

    let smart_source = click_source.replace("frame() using {};", "frame();");
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(&smart_source, &[("increment.c", c_source)])
    });
    let verified = verified.expect("smart frame should select the exact empty mutable candidate");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment.contract"
                    && matches!(name.as_str(), "surface certificate replay" | "frame exact effect check")
        )),
        "the accepted mutable candidate must not be replayed or rechecked: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the smart mutable frame should retain its selected candidate");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [
                        ProofTactic::StepUsing(_),
                        ProofTactic::StepUsing(_),
                        ProofTactic::FrameUsing { region: None, premises }
                    ] if premises.is_empty()
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        &smart_source,
        &[("increment.c", c_source)],
        "increment",
        CProofClaim::Grouped,
    )
    .expect("the smart mutable frame should expand");
    verify_c0_sources(&expanded, &[("increment.c", c_source)])
        .expect("the selected empty mutable frame should independently replay");
}

#[test]
fn contextual_mutable_frame_inside_open_applies_explicit_candidate_on_proof() {
    let c_source = r#"
        int32 write_in_bounds(int32 p[], int32 i, int32 n) {
            p[i] = 9;
            return 0;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "write_in_bounds.c";

        int32 write_in_bounds(int32 p[], int32 i, int32 n) {
            requires n >= 0;
            requires n <= 2147483647;
            requires i >= 0;
            requires i < n;
            owns marker(n);
            consumes p[0..n];
            mutable p[0..n];
            ensures result == 0;
        } by {
            open(marker(n)) {
                execute();
                frame();
            }
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("write_in_bounds.c", c_source)])
    });
    let verified = verified.expect("contextual frame should submit its selected Proof candidate");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "write_in_bounds.contract" && name == "surface certificate replay"
        )),
        "the contextual candidate must not use ordinary surface replay: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the contextual frame should retain its selected simple steps");
    let Some(ProofTactic::Open(open)) = tactics.first() else {
        panic!("{tactics:#?}");
    };
    assert!(
        matches!(
            open.tactics.last(),
            Some(ProofTactic::FrameUsing { region: None, premises }) if !premises.is_empty()
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("write_in_bounds.c", c_source)],
        "write_in_bounds",
        CProofClaim::Grouped,
    )
    .expect("the contextual Proof-owned frame should expand");
    verify_c0_sources(&expanded, &[("write_in_bounds.c", c_source)])
        .expect("the contextual frame candidate should independently replay");
}

#[test]
fn top_level_contextual_frame_applies_explicit_candidate_on_proof() {
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
            mutable p[0..n];
            ensures result == 0;
        } by {
            execute();
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("write_in_bounds.c", c_source)])
    });
    let verified = verified.expect("top-level contextual frame should advance through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "write_in_bounds.contract"
                    && name == "surface certificate replay"
        )),
        "the top-level contextual candidate must not use ordinary surface replay: {events:#?}"
    );
    assert_eq!(
        events
            .iter()
            .filter(|event| matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                    if claim == "write_in_bounds.contract" && name == "frame exact effect check"
            ))
            .count(),
        1,
        "only the whole-certificate gate may recheck the retained frame: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the top-level contextual frame should retain its simple candidate");
    assert!(matches!(
        tactics.iter().find(|tactic| matches!(tactic, ProofTactic::FrameUsing { .. })),
        Some(ProofTactic::FrameUsing { region: None, premises }) if !premises.is_empty()
    ));
    let expanded = expand_c0_claim_source(
        click_source,
        &[("write_in_bounds.c", c_source)],
        "write_in_bounds",
        CProofClaim::Grouped,
    )
    .expect("the top-level contextual frame should expand");
    verify_c0_sources(&expanded, &[("write_in_bounds.c", c_source)])
        .expect("the retained top-level contextual frame should independently replay");

    let frame_offset = click_source
        .find("frame();")
        .expect("proof should contain the selected frame");
    let line = click_source[..frame_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = frame_offset
        - click_source[..frame_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let selected = expand_c0_tactic_source_at(
        click_source,
        &[("write_in_bounds.c", c_source)],
        line,
        column,
    )
    .expect("the deferred Proof-owned frame should expand by itself");
    verify_c0_sources(&selected, &[("write_in_bounds.c", c_source)])
        .expect("the selected deferred frame certificate should independently replay");
}

#[test]
fn top_level_proof_owned_frame_retains_deferred_source_order() {
    let c_source = r#"
        int32 preserve_storage(int32 p[]) {
            return 0;
        }
    "#;
    let click_source = r#"
        resource storage(p: int32*) {
            owns p[0..1];
        }

        verifying "preserve_storage.c";

        int32 preserve_storage(int32 p[]) {
            consumes p[0..1];
            produces storage(p);
            immutable;
            ensures result == 0;
        } by {
            execute();
            fold(storage(p));
            frame();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("preserve_storage.c", c_source)])
        .expect("Proof-owned frame should remain after the deferred fold");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its expansion");
    let fold_index = tactics
        .iter()
        .position(|tactic| matches!(tactic, ProofTactic::FoldResource(_)))
        .expect("the expansion should retain the fold");
    let frame_index = tactics
        .iter()
        .position(|tactic| matches!(tactic, ProofTactic::FrameUsing { .. }))
        .expect("the expansion should retain the frame");
    assert!(fold_index < frame_index, "{tactics:#?}");

    let expanded = expand_c0_claim_source(
        click_source,
        &[("preserve_storage.c", c_source)],
        "preserve_storage",
        CProofClaim::Grouped,
    )
    .expect("the ordered Proof-owned frame should expand");
    verify_c0_sources(&expanded, &[("preserve_storage.c", c_source)])
        .expect("the retained deferred order should independently replay");
}

#[test]
fn smart_execute_crosses_terminal_c_branch_before_checked_frame() {
    let c_source = r#"
        int32 write_selected(int32 p[2], int32 flag) {
            if (flag) {
                p[0] = 1;
            } else {
                p[1] = 1;
            }
            return 0;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "write_selected.c";

        int32 write_selected(int32 p[2], int32 flag) {
            owns marker(flag);
            consumes p[0..2];
            mutable p[0..2];
            ensures result == 0;
        } by {
            open(marker(flag)) {
                execute();
                frame();
            }
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("write_selected.c", c_source)])
    });
    let verified = verified.expect("smart execute should retain both checked terminal C arms");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "write_selected.contract" && name == "surface certificate replay"
        )),
        "branched execute and its common frame must not use ordinary surface replay: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the terminal execution branch should retain its checked certificate");
    let Some(ProofTactic::Open(open)) = tactics.first() else {
        panic!("{tactics:#?}");
    };
    assert!(
        matches!(open.tactics.as_slice(), [ProofTactic::If(_), ProofTactic::FrameUsing { region: None, premises }] if premises.is_empty()),
        "the common exact frame should follow the retained execution branch: {tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("write_selected.c", c_source)],
        "write_selected",
        CProofClaim::Grouped,
    )
    .expect("branched execute with common frame should expand");
    verify_c0_sources(&expanded, &[("write_selected.c", c_source)])
        .expect("the retained execution branch should independently replay");
}

#[test]
fn smart_execute_retains_nested_terminal_c_branches_before_checked_frame() {
    let c_source = r#"
        int32 write_nested(int32 p[2], int32 first, int32 second) {
            if (first) {
                if (second) {
                    p[0] = 1;
                } else {
                    p[1] = 1;
                }
            } else {
                p[0] = 2;
            }
            return 0;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "write_nested.c";

        int32 write_nested(int32 p[2], int32 first, int32 second) {
            owns marker(first);
            consumes p[0..2];
            mutable p[0..2];
            ensures result == 0;
        } by {
            open(marker(first)) {
                execute();
                frame();
            }
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("write_nested.c", c_source)])
    });
    let verified = verified.expect("smart execute should retain nested checked C branches");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "write_nested.contract" && name == "surface certificate replay"
        )),
        "nested execute and its common frame must not use ordinary surface replay: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the nested execution branch should retain its checked certificate");
    let Some(ProofTactic::Open(open)) = tactics.first() else {
        panic!("{tactics:#?}");
    };
    let [
        ProofTactic::If(outer),
        ProofTactic::FrameUsing {
            region: None,
            premises,
        },
    ] = open.tactics.as_slice()
    else {
        panic!("the common frame should follow one retained outer branch: {tactics:#?}");
    };
    assert!(premises.is_empty(), "{tactics:#?}");
    assert!(
        outer
            .then_tactics
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::If(_))),
        "the outer then arm should retain its nested checked branch: {tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("write_nested.c", c_source)],
        "write_nested",
        CProofClaim::Grouped,
    )
    .expect("nested branched execute with common frame should expand");
    verify_c0_sources(&expanded, &[("write_nested.c", c_source)])
        .expect("the retained nested execution branches should independently replay");
}

#[test]
fn contextual_frame_checks_path_specific_evidence_on_partitioned_outcomes() {
    let c_source = r#"
        int32 write_conditionally_indexed(int32 p[1], int32 index) {
            if (index == 0) {
                p[index] = 1;
            } else {
                p[0] = 2;
            }
            return 0;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "write_conditionally_indexed.c";

        int32 write_conditionally_indexed(int32 p[1], int32 index) {
            owns marker(index);
            consumes p[0..1];
            mutable p[0..1];
            ensures result == 0;
        } by {
            open(marker(index)) {
                execute();
                frame();
            }
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("write_conditionally_indexed.c", c_source)])
    });
    let verified =
        verified.expect("path-specific frame evidence should check on outcome partitions");
    let forbidden_operations = events
        .iter()
        .filter_map(|event| match event {
            crate::instrumentation::VerificationEvent::OperationFinished {
                claim, name, ..
            } if claim == "write_conditionally_indexed.contract"
                && matches!(
                    name.as_str(),
                    "surface certificate replay" | "frame exact effect check"
                ) =>
            {
                Some(name.as_str())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        forbidden_operations.is_empty(),
        "partitioned frame search must neither replay nor recheck its checked Proof arms: {forbidden_operations:?}"
    );
    let resource_transitions = events
        .iter()
        .filter(|event| {
            matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                    if claim == "write_conditionally_indexed.contract"
                        && name == "frame resource transition"
            )
        })
        .count();
    assert_eq!(
        resource_transitions, 4,
        "source verification and the independent expansion gate must each transition both original outcomes once"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("partitioned frame should retain an expansion");
    let Some(ProofTactic::Open(open)) = tactics.first() else {
        panic!("{tactics:#?}");
    };
    let frame_branch = open
        .tactics
        .iter()
        .rev()
        .find_map(|tactic| match tactic {
            ProofTactic::If(proof_if)
                if matches!(
                    proof_if.then_tactics.last(),
                    Some(ProofTactic::FrameUsing { region: None, .. })
                ) && matches!(
                    proof_if.else_tactics.last(),
                    Some(ProofTactic::FrameUsing { region: None, .. })
                ) =>
            {
                Some(proof_if)
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("frame evidence should remain branch-local: {tactics:#?}"));
    assert!(
        frame_branch
            .then_tactics
            .iter()
            .chain(&frame_branch.else_tactics)
            .any(|tactic| matches!(tactic, ProofTactic::Have(_))),
        "one outcome partition should retain its explicit derived bound: {tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("write_conditionally_indexed.c", c_source)],
        "write_conditionally_indexed",
        CProofClaim::Grouped,
    )
    .expect("partitioned contextual frame should expand");
    verify_c0_sources(&expanded, &[("write_conditionally_indexed.c", c_source)])
        .expect("the retained outcome-partition certificate should independently replay");
}

#[test]
fn linear_execute_until_inside_open_stops_on_checked_frontier() {
    let c_source = r#"
        int32 three_steps(int32 x) {
            int32 value = x;
            value = value;
            return value;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "three_steps.c";

        int32 three_steps(int32 x) {
            owns marker(x);
            immutable;
            ensures result == x;
        } by {
            open(marker(x)) {
                execute_until(statement(2));
                step();
            }
            step();
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("three_steps.c", c_source)])
    });
    let verified = verified.expect("execute_until should advance the checked open frontier");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "three_steps.contract" && name == "surface certificate replay"
        )),
        "scoped execute_until must retain its checked statement path: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its stopped frontier path");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [
                        ProofTactic::StepUsing(_),
                        ProofTactic::StepUsing(_),
                        ProofTactic::StepUsing(_)
                    ]
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("three_steps.c", c_source)],
        "three_steps",
        CProofClaim::Grouped,
    )
    .expect("the grouped scoped execute_until should expand");
    verify_c0_sources(&expanded, &[("three_steps.c", c_source)])
        .expect("the retained stopped-frontier steps should independently replay");
}

#[test]
fn linear_open_have_retains_the_selected_theorem_application() {
    let c_source = r#"
        int32 two_steps(int32 x) {
            x = x;
            return x;
        }
    "#;
    let click_source = r#"
        theorem int32_reflexive(value: int32) {
            ensures value == value by {
                normalize();
            }
        }

        resource marker(x: int32) {
            fact x == x;
        }

        verifying "two_steps.c";

        int32 two_steps(int32 x) {
            owns marker(x);
            immutable;
            ensures result == x;
        } by {
            open(marker(x)) {
                have x == x by {
                    apply(int32_reflexive(x));
                }
                step();
            }
            step();
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("two_steps.c", c_source)])
    });
    let verified = verified.expect("the nested theorem application should advance the open Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "two_steps.contract" && name == "surface certificate replay"
        )),
        "ordinary nested-scope construction must not replay its retained theorem step: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its nested expansion");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [ProofTactic::Have(have), ProofTactic::StepUsing(_)]
                        if matches!(
                            &have.proof,
                            SourceProof::Script(body)
                                if matches!(
                                    body.as_slice(),
                                    [ProofTactic::ApplyTheoremUsing { application, premises }]
                                        if application.name == "int32_reflexive" && premises.is_empty()
                                )
                        )
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("two_steps.c", c_source)],
        "two_steps",
        CProofClaim::Grouped,
    )
    .expect("the grouped nested open proof should expand");
    verify_c0_sources(&expanded, &[("two_steps.c", c_source)])
        .expect("the retained nested theorem application should independently replay");
}

#[test]
fn linear_open_retains_a_direct_bare_theorem_application() {
    let c_source = r#"
        int32 retain_lower(int32 lower, int32 upper) {
            return lower;
        }
    "#;
    let click_source = r#"
        resource ordered(lower: int32, upper: int32) {
            fact lower < upper;
        }

        verifying "retain_lower.c";

        int32 retain_lower(int32 lower, int32 upper) {
            owns ordered(lower, upper);
            immutable;
            ensures lower <= upper;
        } by {
            open(ordered(lower, upper)) {
                apply(int32_lt_implies_le(lower, upper));
                step();
            }
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("retain_lower.c", c_source)])
    });
    let verified = verified.expect("the direct theorem application should advance the open Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "retain_lower.contract" && name == "surface certificate replay"
        )),
        "ordinary open-scope theorem search must not replay its retained step: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked open proof should retain its expansion");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [
                        ProofTactic::ApplyTheoremUsing { application, premises },
                        ProofTactic::StepUsing(_),
                    ] if application.name == "int32_lt_implies_le" && premises.len() == 1
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("retain_lower.c", c_source)],
        "retain_lower",
        CProofClaim::Grouped,
    )
    .expect("the retained open-scope theorem application should expand");
    verify_c0_sources(&expanded, &[("retain_lower.c", c_source)])
        .expect("the explicit open-scope theorem step should independently re-derive");
}

#[test]
fn linear_open_retains_a_direct_bare_fact_transport() {
    let c_source = r#"
        int32 set_second_return_first(int32 p[2]) {
            p[1] = 9;
            return p[0];
        }
    "#;
    let click_source = r#"
        resource first_is_seven(p: int32[]) {
            owns p[0..2];
            fact p[0] == 7;
        }

        verifying "set_second_return_first.c";

        int32 set_second_return_first(int32 p[2]) {
            owns first_is_seven(p);
            mutable p[1..2];
            ensures result == 7;
        } by {
            open(first_is_seven(p)) {
                step();
                transport(old(p[0]) == 7, p[0] == 7);
                step();
            }
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("set_second_return_first.c", c_source)])
    });
    let verified = verified.expect("the direct transport should advance the open Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "set_second_return_first.contract"
                    && name == "surface certificate replay"
        )),
        "ordinary open-scope transport search must not replay its retained step: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked open transport should retain its expansion");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [
                        ProofTactic::StepUsing(_),
                        ProofTactic::TransportUsing { premises, .. },
                        ProofTactic::StepUsing(_),
                    ] if !premises.is_empty()
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("set_second_return_first.c", c_source)],
        "set_second_return_first",
        CProofClaim::Grouped,
    )
    .expect("the retained open-scope transport should expand");
    verify_c0_sources(&expanded, &[("set_second_return_first.c", c_source)])
        .expect("the explicit open-scope transport should independently re-derive");
}

#[test]
fn branch_interface_retains_its_checked_abstract_join() {
    let c_source = r#"
        int32 nonnegative(int32 x) {
            if (x < 0) {
                x = 1;
            } else {
                x = 2;
            }
            return x;
        }
    "#;
    let click_source = r#"
        verifying "nonnegative.c";

        int32 nonnegative(int32 x) {
            immutable;
            ensures result >= 0;
        } by {
            branch {
                ensuring {
                    fact x >= 0;
                }
                then { step(); }
                else { step(); }
            }
            step();
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("nonnegative.c", c_source)])
    });
    let verified = verified.expect("the checked branch interface should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "nonnegative.contract"
                    && matches!(name.as_str(), "surface certificate replay" | "frame exact effect check")
        )),
        "the branch, common return, and frame must retain one checked Proof: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked branch interface should retain an expansion");
    assert!(
        matches!(
            tactics.as_slice(),
            [
                ProofTactic::Branch(branch),
                ProofTactic::StepUsing(_),
                ProofTactic::FrameUsing { .. },
                ..
            ] if matches!(
                branch.ensuring.as_deref(),
                Some([ProofAssertion::Fact(ClickProposition::Comparison {
                    operator: ComparisonOperator::GreaterEqual,
                    ..
                })])
            ) && matches!(branch.then_tactics.as_slice(), [ProofTactic::StepUsing(_)])
                && matches!(branch.else_tactics.as_slice(), [ProofTactic::StepUsing(_)])
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("nonnegative.c", c_source)],
        "nonnegative",
        CProofClaim::Grouped,
    )
    .expect("the retained branch interface should expand");
    verify_c0_sources(&expanded, &[("nonnegative.c", c_source)])
        .expect("the retained branch-interface certificate should independently re-derive");
}

#[test]
fn branch_interface_retains_exact_unchanged_ownership() {
    let c_source = r#"
        int32 preserve_marker(int32 x, int32 flag) {
            int32 y;
            if (flag != 0) {
                y = 1;
            } else {
                y = 2;
            }
            return x;
        }
    "#;
    let click_source = r#"
        abstract resource marker(x: int32);

        verifying "preserve_marker.c";

        int32 preserve_marker(int32 x, int32 flag) {
            owns marker(x);
            immutable;
            ensures result == x;
        } by {
            step();
            branch {
                ensuring {
                    fact y >= 0;
                    owns marker(x);
                }
                then { step(); }
                else { step(); }
            }
            step();
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("preserve_marker.c", c_source)])
    });
    let verified = verified.expect("the exact owned interface should stay on Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "preserve_marker.contract"
                    && name == "surface certificate replay"
        )),
        "an unchanged exact ownership export must retain its checked Proof: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the exact owned interface should retain an expansion");
    assert!(
        matches!(
            tactics.get(1),
            Some(ProofTactic::Branch(branch))
                if matches!(
                    branch.ensuring.as_deref(),
                    Some([
                        ProofAssertion::Fact(_),
                        ProofAssertion::Resource(ResourceClause::Declared {
                            access: ResourceAccessMode::Own,
                            name,
                            ..
                        }),
                    ]) if name == "marker"
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("preserve_marker.c", c_source)],
        "preserve_marker",
        CProofClaim::Grouped,
    )
    .expect("the retained exact owned interface should expand");
    verify_c0_sources(&expanded, &[("preserve_marker.c", c_source)])
        .expect("the exact owned interface should independently re-derive");
}

#[test]
fn branch_interface_normalizes_an_entailed_owned_quantity_on_proof() {
    let c_source = r#"
        int32 preserve_two_markers(int32 x, int32 flag) {
            int32 y;
            if (flag != 0) {
                y = 1;
            } else {
                y = 2;
            }
            return x;
        }
    "#;
    let click_source = r#"
        abstract resource marker(x: int32);

        verifying "preserve_two_markers.c";

        int32 preserve_two_markers(int32 x, int32 flag) {
            owns 2 of marker(x);
            immutable;
            ensures result == x;
        } by {
            step();
            branch {
                ensuring {
                    fact y >= 0;
                    owns marker(x);
                }
                then { step(); }
                else { step(); }
            }
            step();
            frame();
            simp();
        }
    "#;

    let ((verified, events), checked_interface_joins) =
        crate::lang::click::proof::count_checked_execution_interface_joins(|| {
            crate::instrumentation::collect(|| {
                verify_c0_sources(click_source, &[("preserve_two_markers.c", c_source)])
            })
        });
    let verified = verified.expect("the entailed quantity interface should stay on Proof");
    assert!(
        checked_interface_joins > 0,
        "the quantity interface must reach the checked two-arm Proof join"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "preserve_two_markers.contract"
                    && name == "surface certificate replay"
        )),
        "quantity-interface construction must not replay its surface certificate: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the quantity interface should retain an expansion");
    assert!(matches!(
        tactics.get(1),
        Some(ProofTactic::Branch(branch))
            if matches!(
                branch.ensuring.as_deref(),
                Some([
                    ProofAssertion::Fact(_),
                    ProofAssertion::Resource(ResourceClause::Declared {
                        access: ResourceAccessMode::Own,
                        name,
                        ..
                    }),
                ]) if name == "marker"
            )
    ));

    let expanded = expand_c0_claim_source(
        click_source,
        &[("preserve_two_markers.c", c_source)],
        "preserve_two_markers",
        CProofClaim::Grouped,
    )
    .expect("the retained quantity interface should expand");
    verify_c0_sources(&expanded, &[("preserve_two_markers.c", c_source)])
        .expect("the normalized quantity interface should independently re-derive");
}

#[test]
fn branch_arms_retain_bare_theorem_applications_on_proof() {
    let c_source = r#"
        int32 retain_order(int32 lower, int32 upper, int32 flag) {
            int32 choice;
            if (flag != 0) {
                choice = lower;
            } else {
                choice = upper;
            }
            return choice;
        }
    "#;
    let click_source = r#"
        verifying "retain_order.c";

        int32 retain_order(int32 lower, int32 upper, int32 flag) {
            requires lower < upper;
            immutable;
            ensures lower <= upper;
        } by {
            step();
            branch {
                ensuring {
                    fact lower <= upper;
                }
                then {
                    step();
                    apply(int32_lt_implies_le(lower, upper));
                }
                else {
                    step();
                    apply(int32_lt_implies_le(lower, upper));
                }
            }
            step();
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("retain_order.c", c_source)])
    });
    let verified = verified.expect("bare arm applications should advance the branch Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "retain_order.contract" && name == "surface certificate replay"
        )),
        "ordinary branch theorem search must not replay its retained applications: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked theorem applications should retain an expansion");
    assert!(
        matches!(
            tactics.get(1),
            Some(ProofTactic::Branch(branch))
                if matches!(
                    branch.then_tactics.as_slice(),
                    [ProofTactic::StepUsing(_), ProofTactic::ApplyTheoremUsing { application, premises }]
                        if application.name == "int32_lt_implies_le" && premises.len() == 1
                ) && matches!(
                    branch.else_tactics.as_slice(),
                    [ProofTactic::StepUsing(_), ProofTactic::ApplyTheoremUsing { application, premises }]
                        if application.name == "int32_lt_implies_le" && premises.len() == 1
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("retain_order.c", c_source)],
        "retain_order",
        CProofClaim::Grouped,
    )
    .expect("the retained branch applications should expand");
    verify_c0_sources(&expanded, &[("retain_order.c", c_source)])
        .expect("the explicit branch applications should independently re-derive");
}

#[test]
fn branch_join_retains_a_bare_theorem_application_in_its_continuation() {
    let c_source = r#"
        int32 choose_bound(int32 lower, int32 upper, int32 flag) {
            int32 choice;
            if (flag != 0) {
                choice = lower;
            } else {
                choice = upper;
            }
            return choice;
        }
    "#;
    let click_source = r#"
        verifying "choose_bound.c";

        int32 choose_bound(int32 lower, int32 upper, int32 flag) {
            requires lower < upper;
            immutable;
            ensures lower <= upper;
        } by {
            step();
            branch {
                ensuring {
                    fact lower < upper;
                }
                then { step(); }
                else { step(); }
            }
            apply(int32_lt_implies_le(lower, upper));
            step();
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("choose_bound.c", c_source)])
    });
    let verified =
        verified.expect("the common theorem application should advance the joined Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "choose_bound.contract"
                    && matches!(name.as_str(), "surface certificate replay" | "frame exact effect check")
        )),
        "the branch, theorem, return, and frame must retain one checked Proof: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked common theorem application should retain an expansion");
    assert!(
        matches!(
            tactics.as_slice(),
            [
                ProofTactic::StepUsing(_),
                ProofTactic::Branch(branch),
                ProofTactic::ApplyTheoremUsing { application, premises },
                ProofTactic::StepUsing(_),
                ProofTactic::FrameUsing { region: None, premises: frame_premises },
                ..
            ] if matches!(
                    branch.ensuring.as_deref(),
                    Some([ProofAssertion::Fact(ClickProposition::Comparison {
                        operator: ComparisonOperator::LessThan,
                        ..
                    })])
                )
                && matches!(branch.then_tactics.as_slice(), [ProofTactic::StepUsing(_)])
                && matches!(branch.else_tactics.as_slice(), [ProofTactic::StepUsing(_)])
                && application.name == "int32_lt_implies_le"
                && premises.len() == 1
                && frame_premises.is_empty()
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("choose_bound.c", c_source)],
        "choose_bound",
        CProofClaim::Grouped,
    )
    .expect("the retained common theorem application should expand");
    verify_c0_sources(&expanded, &[("choose_bound.c", c_source)])
        .expect("the explicit common theorem step should independently re-derive");
}

#[test]
fn branch_join_retains_a_bare_fact_transport_in_its_continuation() {
    let c_source = r#"
        int32 choose_bound_transport(int32 lower, int32 upper, int32 flag) {
            int32 choice;
            if (flag != 0) {
                choice = lower;
            } else {
                choice = upper;
            }
            return choice;
        }
    "#;
    let click_source = r#"
        verifying "choose_bound_transport.c";

        int32 choose_bound_transport(int32 lower, int32 upper, int32 flag) {
            requires lower < upper;
            immutable;
            ensures lower < upper;
        } by {
            step();
            branch {
                ensuring {
                    fact old(lower) < old(upper);
                }
                then { step(); }
                else { step(); }
            }
            transport(old(lower) < old(upper), lower < upper);
            step();
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("choose_bound_transport.c", c_source)])
    });
    let verified = verified.expect("the common fact transport should advance the joined Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "choose_bound_transport.contract"
                    && matches!(name.as_str(), "surface certificate replay" | "frame exact effect check")
        )),
        "the branch, transport, return, and frame must retain one checked Proof: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked common fact transport should retain an expansion");
    assert!(
        matches!(
            tactics.as_slice(),
            [
                ProofTactic::StepUsing(_),
                ProofTactic::Branch(branch),
                ProofTactic::TransportUsing { premises, .. },
                ProofTactic::StepUsing(_),
                ProofTactic::FrameUsing { region: None, premises: frame_premises },
                ..
            ] if matches!(
                    branch.ensuring.as_deref(),
                    Some([ProofAssertion::Fact(ClickProposition::Comparison {
                        operator: ComparisonOperator::LessThan,
                        ..
                    })])
                )
                && matches!(branch.then_tactics.as_slice(), [ProofTactic::StepUsing(_)])
                && matches!(branch.else_tactics.as_slice(), [ProofTactic::StepUsing(_)])
                && !premises.is_empty()
                && frame_premises.is_empty()
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("choose_bound_transport.c", c_source)],
        "choose_bound_transport",
        CProofClaim::Grouped,
    )
    .expect("the retained common fact transport should expand");
    verify_c0_sources(&expanded, &[("choose_bound_transport.c", c_source)])
        .expect("the explicit common transport step should independently re-derive");
}

#[test]
fn branch_join_retains_a_nested_have_in_its_continuation() {
    let c_source = r#"
        int32 select_positive(int32 flag) {
            int32 selected;
            if (flag != 0) {
                selected = 1;
            } else {
                selected = 2;
            }
            selected = selected + 1;
            return selected;
        }
    "#;
    let click_source = r#"
        verifying "select_positive.c";

        int32 select_positive(int32 flag) {
            immutable;
            ensures result >= 0;
        } by {
            step();
            branch {
                ensuring {
                    fact selected > 0;
                    fact selected < 2147483647;
                }
                then { step(); }
                else { step(); }
            }
            have selected >= 0 by {
                apply(int32_strictly_positive_is_nonnegative(selected));
            }
            execute_until(statement(5));
            step();
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("select_positive.c", c_source)])
    });
    let verified = verified.expect("the common nested have should advance the joined Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "select_positive.contract"
                    && matches!(name.as_str(), "surface certificate replay" | "frame exact effect check")
        )),
        "the branch, nested have, return, and frame must retain one checked Proof: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked common nested have should retain an expansion");
    assert!(
        matches!(
            tactics.as_slice(),
            [
                ProofTactic::StepUsing(_),
                ProofTactic::Branch(branch),
                ProofTactic::Have(ProofHave {
                    proof: SourceProof::Script(body),
                    ..
                }),
                ProofTactic::StepUsing(_),
                ProofTactic::StepUsing(_),
                ProofTactic::FrameUsing { region: None, premises },
                ..
            ] if matches!(
                    branch.ensuring.as_deref(),
                    Some([
                        ProofAssertion::Fact(ClickProposition::Comparison {
                            operator: ComparisonOperator::GreaterThan,
                            ..
                        }),
                        ProofAssertion::Fact(ClickProposition::Comparison {
                            operator: ComparisonOperator::LessThan,
                            ..
                        }),
                    ])
                )
                && matches!(branch.then_tactics.as_slice(), [ProofTactic::StepUsing(_)])
                && matches!(branch.else_tactics.as_slice(), [ProofTactic::StepUsing(_)])
                && matches!(
                    body.as_slice(),
                    [ProofTactic::ApplyTheoremUsing { application, premises }]
                        if application.name == "int32_strictly_positive_is_nonnegative"
                            && premises.len() == 1
                )
                && premises.is_empty()
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("select_positive.c", c_source)],
        "select_positive",
        CProofClaim::Grouped,
    )
    .expect("the retained common nested have should expand");
    verify_c0_sources(&expanded, &[("select_positive.c", c_source)])
        .expect("the explicit common nested proof should independently re-derive");
}

#[test]
fn branch_join_retains_linear_execute_on_its_common_successor() {
    let c_source = r#"
        int32 select_and_increment(int32 flag) {
            int32 selected;
            if (flag != 0) {
                selected = 1;
            } else {
                selected = 2;
            }
            selected = selected + 1;
            return selected;
        }
    "#;
    let click_source = r#"
        verifying "select_and_increment.c";

        int32 select_and_increment(int32 flag) {
            immutable;
        } by {
            step();
            branch {
                ensuring {
                    fact selected > 0;
                    fact selected < 2147483647;
                }
                then { step(); }
                else { step(); }
            }
            execute();
            frame();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("select_and_increment.c", c_source)])
    });
    let verified = verified.expect("common execute should advance the joined Proof to exit");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "select_and_increment.contract"
                    && matches!(name.as_str(), "surface certificate replay" | "frame exact effect check")
        )),
        "the branch, execute, and frame must retain one checked Proof: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("common execute should retain its checked expansion");
    assert!(
        matches!(
            tactics.as_slice(),
            [
                ProofTactic::StepUsing(_),
                ProofTactic::Branch(branch),
                ProofTactic::StepUsing(_),
                ProofTactic::StepUsing(_),
                ProofTactic::FrameUsing { region: None, premises },
                ..
            ] if matches!(
                    branch.ensuring.as_deref(),
                    Some([
                        ProofAssertion::Fact(ClickProposition::Comparison {
                            operator: ComparisonOperator::GreaterThan,
                            ..
                        }),
                        ProofAssertion::Fact(ClickProposition::Comparison {
                            operator: ComparisonOperator::LessThan,
                            ..
                        }),
                    ])
                )
                && matches!(branch.then_tactics.as_slice(), [ProofTactic::StepUsing(_)])
                && matches!(branch.else_tactics.as_slice(), [ProofTactic::StepUsing(_)])
                && premises.is_empty()
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("select_and_increment.c", c_source)],
        "select_and_increment",
        CProofClaim::Grouped,
    )
    .expect("the retained common execute should expand");
    verify_c0_sources(&expanded, &[("select_and_increment.c", c_source)])
        .expect("the explicit common execute path should independently re-derive");
}

#[test]
fn incremented_strict_lower_bound_retains_its_theorem_path() {
    let c_source = r#"
        int32 select_and_increment_positive(int32 flag) {
            int32 selected;
            if (flag != 0) {
                selected = 1;
            } else {
                selected = 2;
            }
            selected = selected + 1;
            return selected;
        }
    "#;
    let click_source = r#"
        verifying "select_and_increment_positive.c";

        int32 select_and_increment_positive(int32 flag) {
            immutable;
            ensures result > 0;
        } by {
            step();
            branch {
                ensuring {
                    fact selected > 0;
                    fact selected < 2147483647;
                }
                then { step(); }
                else { step(); }
            }
            execute();
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(
            click_source,
            &[("select_and_increment_positive.c", c_source)],
        )
    });
    verified.expect("strict positivity should retain a composed theorem path on Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "select_and_increment_positive.contract"
                    && name == "surface certificate replay"
        )),
        "the typed outcome simp must not ordinarily replay its theorem path: {events:#?}"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &[("select_and_increment_positive.c", c_source)],
        "select_and_increment_positive",
        CProofClaim::Grouped,
    )
    .expect("the strict-positive increment proof should expand");
    assert!(
        expanded.contains("apply(int32_lt_implies_le("),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_increment_strict_greater_lower_bound("),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("select_and_increment_positive.c", c_source)])
        .expect("the retained strict-positive theorem path should independently reverify");
}

#[test]
fn post_execution_have_anchors_strict_increment_theorem_premises() {
    let c_source = r#"
        int32 select_and_increment_positive_have(int32 flag) {
            int32 selected;
            if (flag != 0) {
                selected = 1;
            } else {
                selected = 2;
            }
            selected = selected + 1;
            return selected;
        }
    "#;
    let click_source = r#"
        verifying "select_and_increment_positive_have.c";

        int32 select_and_increment_positive_have(int32 flag) {
            immutable;
            ensures result > 0;
        } by {
            step();
            branch {
                ensuring {
                    fact selected > 0;
                    fact selected < 2147483647;
                }
                then { step(); }
                else { step(); }
            }
            execute();
            frame();
            have result > 0 by simp;
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(
            click_source,
            &[("select_and_increment_positive_have.c", c_source)],
        )
    });
    verified.expect("the post-execution have should retain its composed Proof path");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "select_and_increment_positive_have.contract"
                    && name == "surface certificate replay"
        )),
        "the smart have must not reconstruct and replay its theorem path: {events:#?}"
    );

    let have_offset = click_source
        .find("have result > 0")
        .expect("proof should contain the selected have");
    let position = expansion::position_at_offset(click_source, have_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("select_and_increment_positive_have.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained strict-positive have should expand");
    assert!(!expanded.contains("have result > 0 by simp"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_lt_implies_le("),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_increment_strict_greater_lower_bound("),
        "{expanded}"
    );
    verify_c0_sources(
        &expanded,
        &[("select_and_increment_positive_have.c", c_source)],
    )
    .expect("the expanded strict-positive have should independently reverify");
}

#[test]
fn branch_arms_retain_bare_fact_transports_on_proof() {
    let c_source = r#"
        int32 set_choice_return_first(int32 p[2], int32 flag) {
            if (flag != 0) {
                p[1] = 1;
            } else {
                p[1] = 2;
            }
            return p[0];
        }
    "#;
    let click_source = r#"
        predicate first_is_seven(p: int32[]) {
            p[0] == 7
        }

        verifying "set_choice_return_first.c";

        int32 set_choice_return_first(int32 p[2], int32 flag) {
            requires first_is_seven(p);
            consumes p[0..2];
            mutable p[1..2];
            produces p[0..2];
            ensures result == 7;
        } by {
            unfold(first_is_seven);
            branch {
                ensuring {
                    fact p[0] == 7;
                    owns p[0..2];
                }
                then {
                    step();
                    transport(old(p[0]) == 7, p[0] == 7);
                }
                else {
                    step();
                    transport(old(p[0]) == 7, p[0] == 7);
                }
            }
            step();
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("set_choice_return_first.c", c_source)])
    });
    let verified = verified.expect("bare arm transports should advance the branch Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "set_choice_return_first.contract"
                    && name == "surface certificate replay"
        )),
        "ordinary branch transport search must not replay its retained steps: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked arm transports should retain an expansion");
    assert!(
        matches!(
            tactics.get(1),
            Some(ProofTactic::Branch(branch))
                if matches!(
                    branch.then_tactics.as_slice(),
                    [ProofTactic::StepUsing(_), ProofTactic::TransportUsing { premises, .. }]
                        if !premises.is_empty()
                ) && matches!(
                    branch.else_tactics.as_slice(),
                    [ProofTactic::StepUsing(_), ProofTactic::TransportUsing { premises, .. }]
                        if !premises.is_empty()
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("set_choice_return_first.c", c_source)],
        "set_choice_return_first",
        CProofClaim::Grouped,
    )
    .expect("the retained branch transports should expand");
    verify_c0_sources(&expanded, &[("set_choice_return_first.c", c_source)])
        .expect("the explicit branch transports should independently re-derive");
}

#[test]
fn branch_arms_retain_nested_have_proofs() {
    let c_source = r#"
        int32 select_nonnegative(int32 flag) {
            int32 selected;
            if (flag != 0) {
                selected = 1;
            } else {
                selected = 2;
            }
            return selected;
        }
    "#;
    let click_source = r#"
        theorem int32_reflexive(value: int32) {
            ensures value == value by {
                normalize();
            }
        }

        verifying "select_nonnegative.c";

        int32 select_nonnegative(int32 flag) {
            immutable;
            ensures result >= 0;
        } by {
            step();
            branch {
                ensuring {
                    fact selected >= 0;
                }
                then {
                    step();
                    have selected == selected by {
                        apply(int32_reflexive(selected));
                    }
                }
                else {
                    step();
                    have selected == selected by {
                        apply(int32_reflexive(selected));
                    }
                }
            }
            step();
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("select_nonnegative.c", c_source)])
    });
    let verified = verified.expect("nested arm haves should advance the branch Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "select_nonnegative.contract"
                    && name == "surface certificate replay"
        )),
        "ordinary branch-have construction must not replay its retained scopes: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked branch haves should retain an expansion");
    let retained_have = |tactics: &[ProofTactic]| {
        matches!(
            tactics,
            [ProofTactic::StepUsing(_), ProofTactic::Have(have)]
                if matches!(
                    &have.proof,
                    SourceProof::Script(body)
                        if matches!(
                            body.as_slice(),
                            [ProofTactic::ApplyTheoremUsing { application, premises }]
                                if application.name == "int32_reflexive" && premises.is_empty()
                        )
                )
        )
    };
    assert!(
        matches!(
            tactics.get(1),
            Some(ProofTactic::Branch(branch))
                if retained_have(&branch.then_tactics)
                    && retained_have(&branch.else_tactics)
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("select_nonnegative.c", c_source)],
        "select_nonnegative",
        CProofClaim::Grouped,
    )
    .expect("the retained branch haves should expand");
    verify_c0_sources(&expanded, &[("select_nonnegative.c", c_source)])
        .expect("the explicit nested arm proofs should independently re-derive");
}

#[test]
fn explicit_branch_arms_retain_terminal_execute_search() {
    let c_source = r#"
        int32 choose_one_or_two(int32 flag) {
            if (flag != 0) {
                return 1;
            } else {
                return 2;
            }
        }
    "#;
    let click_source = r#"
        verifying "choose_one_or_two.c";

        int32 choose_one_or_two(int32 flag) {
            immutable;
            ensures result == 1 or result == 2;
        } by {
            branch {
                then {
                    execute();
                }
                else {
                    execute();
                }
            }
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("choose_one_or_two.c", c_source)])
    });
    let verified = verified.expect("terminal arm execution should advance the branch Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "choose_one_or_two.contract"
                    && matches!(name.as_str(), "surface certificate replay" | "frame exact effect check")
        )),
        "terminal arm execution and framing must retain their checked Proof operations: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked terminal arms should retain an expansion");
    let Some(ProofTactic::If(proof_if)) = tactics.first() else {
        panic!("terminal execution branch should retain a logical if: {tactics:#?}");
    };
    for arm in [&proof_if.then_tactics, &proof_if.else_tactics] {
        assert!(
            matches!(
                arm.get(..2),
                Some([ProofTactic::StepUsing(entry), ProofTactic::StepUsing(ret)])
                    if entry.len() == 1 && ret.len() == 1
            ),
            "each terminal arm should begin with checked entry and return steps carrying its path condition: {arm:#?}"
        );
        assert!(
            arm.iter().all(|tactic| !matches!(
                tactic,
                ProofTactic::SmartExecute | ProofTactic::SmartExecuteAllPaths
            )),
            "terminal arm expansion must not retain smart execution: {arm:#?}"
        );
        assert!(
            arm.iter().any(|tactic| matches!(
                tactic,
                ProofTactic::FrameUsing { region: None, premises } if premises.is_empty()
            )),
            "each terminal arm must retain the checked immutable frame: {arm:#?}"
        );
    }
    let expanded = expand_c0_claim_source(
        click_source,
        &[("choose_one_or_two.c", c_source)],
        "choose_one_or_two",
        CProofClaim::Grouped,
    )
    .expect("the retained terminal branch should expand");
    verify_c0_sources(&expanded, &[("choose_one_or_two.c", c_source)])
        .expect("the explicit terminal arm steps should independently re-derive");
}

#[test]
fn transformed_resource_branch_interface_retains_its_common_descendant() {
    let markdown = include_str!("../../../../mdtests/proof_branch_composite_resource_transform.md");
    let mdtest = crate::cli::parse_mdtest(
        std::path::Path::new("proof_branch_composite_resource_transform.md"),
        markdown,
    )
    .expect("the transformed-resource regression should parse");
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("the regression should contain Click source");
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();

    let ((verified, events), checked_interface_joins) =
        crate::lang::click::proof::count_checked_execution_interface_joins(|| {
            crate::instrumentation::collect(|| verify_c0_sources(click_source, &c_sources))
        });
    let verified = verified.expect("the transformed resource branch should stay on Proof");
    assert!(
        checked_interface_joins > 0,
        "the source branch must reach the checked two-arm Proof join"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "select_ready.ensures_0"
                    && name == "surface certificate replay"
        )),
        "the common changed-resource descendant must not be reconstructed by replay: {events:#?}"
    );
    let tactics = verified
        .last()
        .expect("select_ready should be the final verified function")
        .expanded_proof_tactics()
        .expect("the transformed interface should retain an expansion");
    let arm_retains_fold_evidence = |arm: &[ProofTactic]| {
        matches!(
            arm,
            [
                ProofTactic::StepUsing(_),
                ProofTactic::Have(ProofHave {
                    proposition: ClickProposition::Comparison {
                        operator: ComparisonOperator::Equal,
                        ..
                    },
                    proof: SourceProof::Script(proof),
                }),
                ProofTactic::FoldResource(_),
            ] if matches!(proof.as_slice(), [ProofTactic::Assumption])
        )
    };
    assert!(
        matches!(
            tactics.as_slice(),
            [
                ProofTactic::StepUsing(_),
                ProofTactic::Branch(branch),
                ProofTactic::ObserveResource(_),
                ..
            ] if matches!(
                branch.ensuring.as_deref(),
                Some([
                    ProofAssertion::Fact(_),
                    ProofAssertion::Resource(ResourceClause::Declared {
                        access: ResourceAccessMode::Own,
                        name,
                        ..
                    }),
                ]) if name == "ready_bundle"
            ) && arm_retains_fold_evidence(&branch.then_tactics)
                && arm_retains_fold_evidence(&branch.else_tactics)
        ),
        "{tactics:#?}"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &c_sources,
        "select_ready",
        CProofClaim::Ensure(0),
    )
    .expect("the transformed resource branch should expand");
    verify_c0_sources(&expanded, &c_sources)
        .expect("the retained changed-resource interface should independently re-derive");
}

#[test]
fn decided_branch_interface_retains_the_surviving_checked_state() {
    let c_source = r#"
        int32 selected_nonnegative(int32 x) {
            if (x < 0) {
                x = 1;
            } else {
                x = 2;
            }
            return x;
        }
    "#;
    let click_source = r#"
        verifying "selected_nonnegative.c";

        int32 selected_nonnegative(int32 x) {
            requires x < 0;
            immutable;
            ensures result == 1;
        } by {
            branch {
                ensuring {
                    fact x == 1;
                }
                then { step(); }
                else { step(); }
            }
            step();
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("selected_nonnegative.c", c_source)])
    });
    let verified = verified.expect("the sole feasible interface arm should stay on Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "selected_nonnegative.contract" && name == "surface certificate replay"
        )),
        "decided interface construction must retain its checked state directly: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the decided interface should retain an expansion");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Branch(branch))
                if branch.ensuring.is_some()
                    && matches!(branch.then_tactics.as_slice(), [ProofTactic::StepUsing(_)])
                    && branch.else_tactics.is_empty()
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("selected_nonnegative.c", c_source)],
        "selected_nonnegative",
        CProofClaim::Grouped,
    )
    .expect("the decided interface should expand");
    verify_c0_sources(&expanded, &[("selected_nonnegative.c", c_source)])
        .expect("the decided retained interface should independently re-derive");
}

#[test]
fn open_scope_retains_its_checked_branch_interface() {
    let c_source = r#"
        int32 scoped_nonnegative(int32 x) {
            if (x < 0) {
                x = 1;
            } else {
                x = 2;
            }
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "scoped_nonnegative.c";

        int32 scoped_nonnegative(int32 x) {
            owns marker(x);
            immutable;
            ensures result >= 0;
        } by {
            open(marker(x)) {
                branch {
                    ensuring {
                        fact x >= 0;
                    }
                    then { step(); }
                    else { step(); }
                }
                step();
            }
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("scoped_nonnegative.c", c_source)])
    });
    let verified = verified.expect("the scoped branch interface should stay on Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "scoped_nonnegative.contract" && name == "surface certificate replay"
        )),
        "scoped branch-interface construction must retain checked structure: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the scoped branch interface should retain its expansion");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [ProofTactic::Branch(branch), ProofTactic::StepUsing(_)]
                        if branch.ensuring.is_some()
                            && matches!(branch.then_tactics.as_slice(), [ProofTactic::StepUsing(_)])
                            && matches!(branch.else_tactics.as_slice(), [ProofTactic::StepUsing(_)])
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("scoped_nonnegative.c", c_source)],
        "scoped_nonnegative",
        CProofClaim::Grouped,
    )
    .expect("the scoped branch interface should expand");
    verify_c0_sources(&expanded, &[("scoped_nonnegative.c", c_source)])
        .expect("the scoped retained interface should independently re-derive");
}

#[test]
fn open_scope_retains_its_checked_execution_branch() {
    let c_source = r#"
        int32 empty_branch(int32 x) {
            if (x < 0) {
            } else {
            }
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "empty_branch.c";

        int32 empty_branch(int32 x) {
            owns marker(x);
            immutable;
            ensures result == x;
        } by {
            open(marker(x)) {
                branch {
                    then {
                    }
                    else {
                    }
                }
                step();
            }
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("empty_branch.c", c_source)])
    });
    let verified = verified.expect("the execution branch should join inside the open Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "empty_branch.contract" && name == "surface certificate replay"
        )),
        "ordinary scoped branch construction must retain its checked structure: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its scoped branch");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [ProofTactic::Branch(branch), ProofTactic::StepUsing(premises)]
                        if branch.ensuring.is_none()
                            && branch.then_tactics.is_empty()
                            && branch.else_tactics.is_empty()
                            && premises.is_empty()
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("empty_branch.c", c_source)],
        "empty_branch",
        CProofClaim::Grouped,
    )
    .expect("the grouped scoped branch should expand");
    verify_c0_sources(&expanded, &[("empty_branch.c", c_source)])
        .expect("the retained scoped branch should independently replay");
}

#[test]
fn open_scope_retains_a_decided_execution_branch_and_its_continuation() {
    let c_source = r#"
        int32 selected_branch(int32 x) {
            if (x < 0) {
                x = 1;
            } else {
                x = 2;
            }
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "selected_branch.c";

        int32 selected_branch(int32 x) {
            requires x < 0;
            owns marker(x);
            immutable;
            ensures result == 1;
        } by {
            open(marker(x)) {
                branch {
                    then { step(); }
                    else { step(); }
                }
                step();
            }
            frame();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("selected_branch.c", c_source)])
    });
    let verified = verified.expect("the decided execution path should stay inside the open Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "selected_branch.contract" && name == "surface certificate replay"
        )),
        "the scoped decided branch must retain its searched simple steps directly: {events:#?}"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the scoped decided branch should retain its expansion");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [ProofTactic::If(proof_if), ProofTactic::StepUsing(_)]
                        if proof_if.then_tactics.len() == 2
                            && proof_if.else_tactics.is_empty()
                            && matches!(
                                proof_if.then_tactics.first(),
                                Some(ProofTactic::StepUsing(premises)) if !premises.is_empty()
                            )
                )
        ),
        "the open child should retain the closed decided node followed by its continuation: {tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("selected_branch.c", c_source)],
        "selected_branch",
        CProofClaim::Grouped,
    )
    .expect("the scoped decided branch should expand");
    verify_c0_sources(&expanded, &[("selected_branch.c", c_source)])
        .expect("the scoped decided certificate should independently re-derive the proof");
}

#[test]
fn automatic_terminal_branch_retains_its_checked_proof_outcomes() {
    let c_source = r#"
            int32 choose(int32 value) {
                if (value < 0) {
                    return 1;
                } else {
                    return 2;
                }
            }
        "#;
    let click_source = r#"
            verifying "choose.c";

            int32 choose(int32 value) {
                ensures result == 1 or result == 2;
            } by {
                execute();
                simp();
            }
        "#;

    let ((verified, events), planning_transitions) = count_planning_statement_transitions(|| {
        crate::instrumentation::collect(|| {
            verify_c0_sources(click_source, &[("choose.c", c_source)])
        })
    });
    let verified = verified.expect("automatic terminal branch should verify");
    assert_eq!(
        planning_transitions, 0,
        "the automatic terminal branch must search only on checked Proof descendants"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "choose.contract"
                    && name == "smart tactic compatibility replay (tactic 0, source 0)"
        )),
        "terminal branch construction must bypass compatibility replay: {events:#?}"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("terminal branch should retain an expansion");
    let Some(ProofTactic::If(proof_if)) = expanded.first() else {
        panic!("terminal branch should expand as a logical if: {expanded:#?}");
    };
    for (name, arm) in [
        ("then", &proof_if.then_tactics),
        ("else", &proof_if.else_tactics),
    ] {
        assert!(
            matches!(arm.first(), Some(ProofTactic::StepUsing(premises)) if premises.len() == 1),
            "{name} arm should retain the explicit C-branch entry condition: {arm:#?}"
        );
        assert!(
            matches!(arm.get(1), Some(ProofTactic::StepUsing(_))),
            "{name} arm should retain its checked return step: {arm:#?}"
        );
        assert!(
            arm.iter().all(|tactic| !matches!(
                tactic,
                ProofTactic::SmartExecute
                    | ProofTactic::SmartExecuteAllPaths
                    | ProofTactic::ExecuteUntil(_)
                    | ProofTactic::Simp
            )),
            "{name} arm expansion must contain only retained simple tactics: {arm:#?}"
        );
    }
    let expanded_source = expand_c0_claim_source(
        click_source,
        &[("choose.c", c_source)],
        "choose",
        CProofClaim::Grouped,
    )
    .expect("terminal branch should expand into source");
    verify_c0_sources(&expanded_source, &[("choose.c", c_source)])
        .expect("the retained terminal branch should independently reverify");
}

#[test]
fn point_smart_have_retains_a_checked_simple_closer() {
    let c_source = r#"
            int32 identity(int32 value) {
                return value;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 value) {
                requires value >= 0;
                ensures result >= 0;
            } by {
                have value >= 0 by auto;
                step();
                assumption();
            }
        "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("checked point smart have should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "surface certificate replay"
        )),
        "the migrated smart have must not pass through ordinary certificate replay: {events:#?}"
    );
}

#[test]
fn point_smart_have_retains_a_checked_theorem_application() {
    let c_source = r#"
            int32 first(int32 x, int32 y, int32 z) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "first.c";

            int32 first(int32 x, int32 y, int32 z) {
                requires x <= y;
                requires y < z;
                ensures result < z;
            } by {
                have x < z by simp;
                execute();
                simp();
            }
        "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("first.c", c_source)])
    });
    verified.expect("checked point smart have should apply signed-order transitivity");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "first.contract" && name == "surface certificate replay"
        )),
        "the migrated theorem-backed have must not ordinarily replay its certificate: {events:#?}"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &[("first.c", c_source)],
        "first",
        CProofClaim::Grouped,
    )
    .expect("the theorem-backed have should expand into simple steps");
    assert!(!expanded.contains("have x < z by simp"), "{expanded}");
    assert!(expanded.contains("have x < z by {"), "{expanded}");
    assert!(expanded.contains("apply"), "{expanded}");
    verify_c0_sources(&expanded, &[("first.c", c_source)])
        .expect("the retained theorem-backed have should independently reverify");
}

#[test]
fn explicit_linear_point_have_uses_the_checked_proof_path() {
    let c_source = r#"
            int32 identity(int32 value) {
                return value;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 value) {
                requires value >= 0;
                ensures result >= 0;
            } by {
                have value >= 0 by {
                    assumption();
                }
                step();
                assumption();
            }
        "#;

    verify_c0_sources(click_source, &[("identity.c", c_source)])
        .expect("explicit point have should advance through its checked simple step");
    let expanded = expand_c0_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Grouped,
    )
    .expect("explicit checked point have should remain expandable");
    assert!(expanded.contains("have value >= 0 by {"));
    assert!(expanded.matches("assumption();").count() >= 2);
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("expanded explicit point have should independently replay");
}

#[test]
fn explicit_post_execution_have_uses_the_checked_outcome_proof_path() {
    let c_source = r#"
            int32 identity(int32 value) {
                return value;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 value) {
                requires value >= 0;
                ensures result >= 0;
            } by {
                execute();
                have result >= 0 by {
                    assumption();
                }
                assumption();
            }
        "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("explicit post-execution have should advance through its outcome Proof");
    let source_verification_events = events.iter().take_while(|event| {
        !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "whole-contract certificate construction"
        )
    });
    assert!(
        source_verification_events
            .into_iter()
            .all(|event| !matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name.starts_with("post-execution simple have replay")
            )),
        "the explicit outcome have must retain its checked Proof without legacy replay: {events:#?}"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Grouped,
    )
    .expect("explicit checked outcome have should remain expandable");
    assert!(expanded.contains("have result >= 0 by {"), "{expanded}");
    assert!(expanded.matches("assumption();").count() >= 2, "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("expanded explicit outcome have should independently replay");
}

#[test]
fn quantified_outcome_simp_keeps_its_binder_on_the_checked_goal() {
    let c_source = r#"
            int32 bounded(int32 value) {
                return value;
            }
        "#;
    let click_source = r#"
            verifying "bounded.c";

            int32 bounded(int32 value) {
                requires wide: forall (k: int32) {
                    0 <= k and k < 3 implies k <= value
                };
                ensures narrow: forall (k: int32) {
                    0 <= k and k < 2 implies k <= value
                };
            } by {
                execute();
                simp();
            }
        "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("bounded.c", c_source)])
    });
    verified.expect("the quantified outcome should verify through Proof");
    let source_verification_events = events.iter().take_while(|event| {
        !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "whole-contract certificate construction"
        )
    });
    assert!(
        source_verification_events
            .into_iter()
            .all(|event| !matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "outcome simp compatibility construction"
            )),
        "the binder-aware outcome certificate must not use compatibility construction: {events:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("bounded.c", c_source)],
        "bounded",
        CProofClaim::Grouped,
    )
    .expect("the quantified outcome proof should expand");
    assert!(expanded.contains("intro();"), "{expanded}");
    assert!(expanded.contains("instantiate("), "{expanded}");
    verify_c0_sources(&expanded, &[("bounded.c", c_source)])
        .expect("the retained binder-aware certificate should replay");
}

#[test]
fn outcome_simp_with_no_open_claims_is_an_empty_proof_transition() {
    let c_source = r#"
        struct object { int32 refs; };

        void release(struct object* obj) {
            obj->refs = 0;
        }
    "#;
    let click_source = r#"
        resource object_ref(obj: struct object*) {
            owns object(obj);
            fact obj->refs == count(object_ref(obj));
        }

        verifying "release.c";

        void release(struct object* obj) {
            requires obj->refs == 1;
            consumes object_ref(obj);
            mutable obj->refs;
        } by {
            unfold(object_ref(obj));
            execute();
            frame();
            simp();
        }
    "#;
    let sources = [("release.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("a final simp with no open claims should be a no-op");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp legacy exit planning"
        )),
        "an empty claim set must not enter legacy exit planning: {events:#?}"
    );
    let expanded = expand_c0_claim_source(click_source, &sources, "release", CProofClaim::Grouped)
        .expect("the empty outcome transition should expand");
    let release_proof = expanded
        .split("void release")
        .nth(1)
        .expect("expanded release proof should exist");
    assert!(!release_proof.contains("simp();"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the expansion without the empty simp should replay");
}

#[test]
fn outcome_predicate_unfold_relowers_resource_counts_on_the_checked_proof() {
    let c_source = r#"
        struct pool { int32 checked_out; int32 capacity; };

        void init(struct pool* pool, int32 capacity) {
            pool->checked_out = 0;
            pool->capacity = capacity;
        }
    "#;
    let click_source = r#"
        resource pool_object(pool: struct pool*) {}

        resource pool_slot(pool: struct pool*) {
            views object(pool);
        }

        predicate valid_pool(pool: struct pool*) {
            0 <= pool->checked_out and
            pool->checked_out == count(pool_object(pool)) and
            pool->capacity == pool->checked_out + count(pool_slot(pool))
        }

        verifying "init.c";

        void init(struct pool* pool, int32 capacity) {
            requires 0 < capacity;
            owns object(pool);
            mutable pool->checked_out, pool->capacity;
            produces capacity of pool_slot(pool);
            ensures valid_pool(pool);
        } by {
            execute();
            fold(capacity of pool_slot(pool));
            frame();
            simp();
        }
    "#;
    let sources = [("init.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the unfolded resource-count goal should close through Proof");
    let compatibility_events = events
        .iter()
        .take_while(|event| {
            !matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "whole-contract certificate construction"
            )
        })
        .filter(|event| {
            matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "outcome simp legacy exit planning"
                        || name == "outcome simp compatibility construction"
            )
        })
        .collect::<Vec<_>>();
    assert!(
        compatibility_events.is_empty(),
        "predicate closure must not enter outcome compatibility planning: {compatibility_events:#?}"
    );

    let expanded = expand_c0_claim_source(click_source, &sources, "init", CProofClaim::Grouped)
        .expect("the retained predicate closure should expand");
    assert!(
        expanded.contains("have valid_pool(pool) by {"),
        "{expanded}"
    );
    assert!(expanded.contains("unfold(valid_pool);"), "{expanded}");
    assert!(expanded.contains("normalize();"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the retained predicate closure should replay independently");
}

#[test]
fn outcome_predicate_unfold_uses_the_checked_frame_population_transition() {
    let c_source = r#"
        struct pool { int32 checked_out; };
        struct object { int32 value; };

        void give_back(struct pool* pool, struct object* object) {
            pool->checked_out = pool->checked_out - 1;
        }
    "#;
    let click_source = r#"
        resource pool_object(pool: struct pool*, object: struct object*) {
            owns object(object);
        }

        predicate valid_pool(pool: struct pool*) {
            0 <= pool->checked_out and
            pool->checked_out == count(pool_object(pool, _))
        }

        verifying "give_back.c";

        void give_back(struct pool* pool, struct object* object) {
            requires valid_pool(pool);
            requires count(pool_object(pool, object)) == 1;
            owns object(pool);
            consumes pool_object(pool, object);
            mutable pool->checked_out;
            produces object(object);
            ensures valid_pool(pool);
        } by {
            unfold(valid_pool);
            unfold(pool_object(pool, object));
            execute();
            frame();
            simp();
        }
    "#;
    let sources = [("give_back.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the checked frame population transition should reach the outcome Proof");
    let compatibility_events = events
        .iter()
        .take_while(|event| {
            !matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "whole-contract certificate construction"
            )
        })
        .filter(|event| {
            matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "outcome simp legacy exit planning"
                        || name == "outcome simp compatibility construction"
            )
        })
        .collect::<Vec<_>>();
    assert!(
        compatibility_events.is_empty(),
        "the live population goal must not enter outcome compatibility planning: {compatibility_events:#?}"
    );

    let expanded =
        expand_c0_claim_source(click_source, &sources, "give_back", CProofClaim::Grouped)
            .expect("the retained population transition should expand");
    assert!(
        expanded.contains(
            "have 0 <= pool->checked_out and pool->checked_out == count(pool_object(pool, _)) by {"
        ),
        "{expanded}"
    );
    assert!(expanded.contains("unfold(valid_pool);"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the retained population transition should replay independently");
}

#[test]
fn outcome_predicate_unfold_provenance_survives_nested_have_expansion() {
    let c_source = r#"
        int32 sort_three_cells(int32 p[3]) {
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
        verifying "sort_three_cells.c";

        int32 sort_three_cells(int32 p[3]) {
            requires loadable(p[0..3]);
            consumes p[0..3];
            ensures permutation(p, old(p), 0, 3) by {
                execute();
                unfold(permutation);
                simp();
            }
        }
    "#;
    let sources = [("sort_three_cells.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the surviving unfold-owned universal should close through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp legacy exit planning"
                    || name == "outcome simp compatibility construction"
        )),
        "the retained predicate body must not enter outcome compatibility planning: {events:#?}"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &sources,
        "sort_three_cells",
        CProofClaim::Ensure(0),
    )
    .expect("the retained nested predicate proof should expand");
    assert!(
        expanded.contains("have permutation(p, old(p), 0, 3) by {"),
        "{expanded}"
    );
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(expanded.contains("unfold(permutation);"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the retained nested predicate proof should replay independently");
}

#[test]
fn bound_universal_outcome_retains_instantiation_and_transport() {
    let c_source = r#"
        int32 bubble_pass3(int32 p[3]) {
            int32 j;
            int32 tmp;
            j = 0;
            while (j < 2) {
                if (p[j + 1] < p[j]) {
                    tmp = p[j];
                    p[j] = p[j + 1];
                    p[j + 1] = tmp;
                }
                j = j + 1;
            }
            return 0;
        }
    "#;
    let click_source = r#"
        verifying "bubble_pass3.c";

        predicate all_le_range(p: int32[], lo: int32, hi: int32, x: int32) {
            forall (k: int32) {
                0 <= k and lo <= k and k < hi implies p[k] <= x
            }
        }

        int32 bubble_pass3(int32 p[3]) {
            requires loadable(p[0..3]);
            consumes p[0..3];
            ensures all_le_range(p, 0, 2, p[2]);
        } by {
            step();
            step();
            step();
            loop {
                invariant j >= 0 and j <= 2;
                invariant all_le_range(p, 0, j, p[j]);
                initialize by {
                    unfold(all_le_range);
                    simp();
                }
                preserve by {
                    unfold(all_le_range);
                }
                mutable p[0..3] by frame;
            }
            step();
            unfold(all_le_range);
            simp();
        }
    "#;
    let sources = [("bubble_pass3.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the bound universal outcome should close through Proof");
    let fallback_events = events
        .iter()
        .filter(|event| {
            matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "outcome simp legacy exit planning"
                        || name == "outcome simp compatibility construction"
            )
        })
        .collect::<Vec<_>>();
    assert!(
        fallback_events.is_empty(),
        "bound universal closure must not enter outcome compatibility planning: {fallback_events:#?}"
    );

    let expanded =
        expand_c0_claim_source(click_source, &sources, "bubble_pass3", CProofClaim::Grouped)
            .expect("the retained bound universal proof should expand");
    assert!(expanded.contains("instantiate("), "{expanded}");
    assert!(expanded.contains("transport("), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the retained bound universal proof should replay independently");
}

#[test]
fn bound_universal_fixture_census_has_no_outcome_fallbacks() {
    for (filename, function) in [
        ("bubble_pass3_max_suffix.md", "bubble_pass3"),
        ("bubble_sort3_two_pass_sorted.md", "bubble_sort3_two_pass"),
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(filename);
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
        let mdtest = crate::cli::parse_mdtest(&path, &source)
            .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
        let click_source = mdtest
            .click_source
            .as_deref()
            .unwrap_or_else(|| panic!("`{}` has no Click source", path.display()));
        let c_sources = mdtest
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let (verified, events) =
            crate::instrumentation::collect(|| verify_c0_sources(click_source, &c_sources));
        verified.unwrap_or_else(|error| panic!("`{}` failed: {error:?}", path.display()));
        let fallback_events = events
            .iter()
            .filter(|event| {
                matches!(
                    event,
                    crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                        if name == "outcome simp legacy exit planning"
                            || name == "outcome simp compatibility construction"
                )
            })
            .collect::<Vec<_>>();
        assert!(
            fallback_events.is_empty(),
            "`{}` entered outcome fallback planning: {fallback_events:#?}",
            path.display()
        );

        let expanded =
            expand_c0_claim_source(click_source, &c_sources, function, CProofClaim::Grouped)
                .unwrap_or_else(|error| panic!("failed to expand `{}`: {error:?}", path.display()));
        verify_c0_sources(&expanded, &c_sources).unwrap_or_else(|error| {
            panic!(
                "expanded proof from `{}` did not replay independently: {error:?}",
                path.display()
            )
        });
    }
}

#[test]
fn snapshot_and_post_call_transport_fixtures_have_no_outcome_fallbacks() {
    for (filename, function, claim, retained_step) in [
        (
            "execute_expands_certified_post_call_fact.md",
            "restore_one",
            CProofClaim::Grouped,
            "rewrite(at(statement(0).entry, cell->value)",
        ),
        (
            "separate_symbolic_unwritten_read.md",
            "write_i_read_j",
            CProofClaim::Ensure(0),
            "transport(old(p[j]) == old(p[j]), result == old(p[j]))",
        ),
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(filename);
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
        let mdtest = crate::cli::parse_mdtest(&path, &source)
            .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
        let click_source = mdtest
            .click_source
            .as_deref()
            .unwrap_or_else(|| panic!("`{}` has no Click source", path.display()));
        let c_sources = mdtest
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let (verified, events) =
            crate::instrumentation::collect(|| verify_c0_sources(click_source, &c_sources));
        verified.unwrap_or_else(|error| panic!("`{}` failed: {error:?}", path.display()));
        let fallback_events = events
            .iter()
            .filter(|event| {
                matches!(
                    event,
                    crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                        if name == "outcome simp legacy exit planning"
                            || name == "outcome simp compatibility construction"
                )
            })
            .collect::<Vec<_>>();
        assert!(
            fallback_events.is_empty(),
            "`{}` entered outcome fallback planning: {fallback_events:#?}",
            path.display()
        );

        let expanded = expand_c0_claim_source(click_source, &c_sources, function, claim)
            .unwrap_or_else(|error| panic!("failed to expand `{}`: {error:?}", path.display()));
        assert!(expanded.contains(retained_step), "{expanded}");
        verify_c0_sources(&expanded, &c_sources).unwrap_or_else(|error| {
            panic!(
                "expanded proof from `{}` did not replay independently: {error:?}",
                path.display()
            )
        });

        let without_retained_step = expanded
            .lines()
            .filter(|line| !line.contains(retained_step))
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            verify_c0_sources(&without_retained_step, &c_sources).is_err(),
            "`{}` replayed after deleting its selected retained step",
            path.display()
        );
        if filename == "separate_symbolic_unwritten_read.md" {
            let without_separation = expanded
                .lines()
                .filter(|line| !line.contains("separate(memory("))
                .collect::<Vec<_>>()
                .join("\n");
            assert!(
                verify_c0_sources(&without_separation, &c_sources).is_err(),
                "`{}` replayed after deleting its required separation premises",
                path.display()
            );
        }
    }
}

#[test]
fn resource_example_pipelines_have_no_outcome_fallbacks() {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    for (project, sidecar, function, retained_step) in [
        (
            "linked-list",
            "linked_list.click",
            "list_roundtrip",
            "have observed == node->value by {",
        ),
        (
            "input-cursor",
            "input_cursor.click",
            "input_cursor_take",
            "transport(at(statement(2).entry, loadable(old(owner->data[0..owner->len])))",
        ),
        (
            "owned-segmented-buffer",
            "owned_segmented_buffer.click",
            "owned_segmented_buffer_swap",
            "apply(int32_successor_le_implies_lt(0, owner->first_len)) using {",
        ),
        (
            "owned-string",
            "owned_string.click",
            "owned_string_init",
            "rewrite(owner->cap == capacity);",
        ),
        (
            "recursive-zero-list",
            "recursive_zero_list.click",
            "zero_list_pipeline",
            "fold(zero_list(first));",
        ),
        (
            "vector-push",
            "vector_push.click",
            "vector_push",
            "apply(int32_increment_preserves_order(",
        ),
    ] {
        let path = manifest.join("examples").join(project).join(sidecar);
        let click_source = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
        let sources = crate::cli::read_verifying_sources(&path, &click_source)
            .unwrap_or_else(|error| panic!("failed to load `{}`: {error}", path.display()));
        let c_sources = crate::cli::source_refs(&sources);

        let (verified, events) =
            crate::instrumentation::collect(|| verify_c0_sources(&click_source, &c_sources));
        verified.unwrap_or_else(|error| panic!("`{}` failed: {error:?}", path.display()));
        let fallback_events = events
            .iter()
            .filter(|event| {
                matches!(
                    event,
                    crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                        if name == "outcome simp legacy exit planning"
                            || name == "outcome simp compatibility construction"
                )
            })
            .collect::<Vec<_>>();
        assert!(
            fallback_events.is_empty(),
            "`{}` entered outcome fallback planning: {fallback_events:#?}",
            path.display()
        );

        let expanded =
            expand_c0_claim_source(&click_source, &c_sources, function, CProofClaim::Grouped)
                .unwrap_or_else(|error| panic!("failed to expand `{}`: {error:?}", path.display()));
        assert!(expanded.contains(retained_step), "{expanded}");
        verify_c0_sources(&expanded, &c_sources).unwrap_or_else(|error| {
            panic!(
                "expanded proof from `{}` did not replay independently: {error:?}",
                path.display()
            )
        });
    }
}

#[test]
fn negative_outcome_diagnostic_manifests_have_no_fallbacks() {
    let manifests = [
        (
            "pure/type",
            &[
                "c_multiplication.md",
                "c_nonzero_integer_rejected_as_pointer.md",
                "contract_let_type_mismatch.md",
                "max_bad_ensure.md",
                "grouped_post_tactics_respect_order.md",
                "grouped_top_level_witness_rejected.md",
            ][..],
        ),
        (
            "memory/mutation",
            &[
                "fill3_bad_memory_postcondition.md",
                "fill_tail_rejects_tail_segment_unchanged.md",
                "forall_array_segment_rejects_overwritten_cell.md",
                "loop_rejects_stale_address_escaped_local.md",
                "loop_rejects_stale_pre_loop_store.md",
                "pointer_params_may_alias_without_separate.md",
                "proof_branch_hides_arm_facts.md",
                "write_second_old_rejects_overwritten_cell.md",
            ][..],
        ),
        (
            "resource/call",
            &[
                "composite_resource_folded_nested_fact_projection.md",
                "composite_resource_nested_observe_not_automatic.md",
                "grouped_fold_after_simp_does_not_close.md",
                "grouped_post_tactics_respect_order.md",
                "grouped_unfold_respects_order.md",
                "opaque_call_does_not_preserve_overlapping_field.md",
                "opaque_call_rejects_weak_postcondition.md",
                "permission_call_consumes_write_without_return.md",
                "resource_summary_requires_returned_write.md",
            ][..],
        ),
    ];
    let mdtests = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests");
    let mut checked = BTreeSet::new();
    for (class, filenames) in manifests {
        for filename in filenames {
            if !checked.insert(*filename) {
                continue;
            }
            let path = mdtests.join(filename);
            let source = std::fs::read_to_string(&path)
                .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
            let mdtest = crate::cli::parse_mdtest(&path, &source)
                .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
            let click_source = mdtest
                .click_source
                .as_deref()
                .unwrap_or_else(|| panic!("`{}` has no Click source", path.display()));
            let c_sources = mdtest
                .c_sources
                .iter()
                .map(|(name, source)| (name.as_str(), source.as_str()))
                .collect::<Vec<_>>();
            let crate::cli::MdTestExpectation::FailContains(expected) = mdtest
                .expectation
                .as_ref()
                .unwrap_or_else(|| panic!("`{}` has no expectation", path.display()))
            else {
                panic!("`{}` is not an expected failure", path.display());
            };

            let (result, events) =
                crate::instrumentation::collect(|| verify_c0_sources(click_source, &c_sources));
            let error = match result {
                Ok(_) => panic!("`{}` unexpectedly verified", path.display()),
                Err(error) => error,
            };
            assert!(
                error.message().contains(expected),
                "{class} fixture `{}` expected `{expected}`, got `{}`",
                path.display(),
                error.message()
            );
            assert!(
                error.message().len() < 16 * 1024,
                "{class} fixture `{}` produced an unbounded diagnostic ({} bytes)",
                path.display(),
                error.message().len()
            );
            let fallback_events = events
                .iter()
                .filter(|event| {
                    matches!(
                        event,
                        crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                            if name == "outcome simp legacy exit planning"
                                || name == "outcome simp compatibility construction"
                    )
                })
                .collect::<Vec<_>>();
            assert!(
                fallback_events.is_empty(),
                "{class} fixture `{}` entered outcome fallback planning: {fallback_events:#?}",
                path.display()
            );
        }
    }
}

#[test]
fn branch_continuation_claims_retain_their_selected_outcome_step() {
    for (filename, function, claim, claim_label) in [
        (
            "proof_branch_continuation.md",
            "joined_increment",
            CProofClaim::Ensure(1),
            "joined_increment.ensures_1",
        ),
        (
            "proof_branch_interface_continuation.md",
            "advance_nested_join",
            CProofClaim::Ensure(0),
            "advance_nested_join.ensures_0",
        ),
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(filename);
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
        let mdtest = crate::cli::parse_mdtest(&path, &source)
            .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
        let click_source = mdtest
            .click_source
            .as_deref()
            .unwrap_or_else(|| panic!("`{}` has no Click source", path.display()));
        let c_sources = mdtest
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let (verified, events) =
            crate::instrumentation::collect(|| verify_c0_sources(click_source, &c_sources));
        verified.unwrap_or_else(|error| panic!("`{}` failed: {error:?}", path.display()));
        let fallback_events = events
            .iter()
            .filter(|event| {
                matches!(
                    event,
                    crate::instrumentation::VerificationEvent::OperationFinished {
                        claim,
                        name,
                        ..
                    } if claim == claim_label
                        && (name == "outcome simp legacy exit planning"
                            || name == "outcome simp compatibility construction")
                )
            })
            .collect::<Vec<_>>();
        assert!(
            fallback_events.is_empty(),
            "`{claim_label}` entered outcome fallback planning: {fallback_events:#?}"
        );
        if filename == "proof_branch_continuation.md" {
            let captured = crate::lang::click::proof::capture_c0_tactic_expansion(
                click_source,
                &c_sources,
                crate::lang::click::expansion::ProofSite::FunctionClaim {
                    function_name: function.to_string(),
                    claim: CProofClaim::Ensure(1),
                },
                0,
            )
            .expect("the selected pre-branch step should have one stable expansion");
            assert!(
                matches!(captured.as_slice(), [ProofTactic::StepUsing(_)]),
                "the selected step absorbed a later structured branch: {captured:#?}"
            );
        }

        let retained_step = "apply(int32_increment_strict_greater_lower_bound(";
        let expanded = expand_c0_claim_source(click_source, &c_sources, function, claim)
            .unwrap_or_else(|error| panic!("failed to expand `{}`: {error:?}", path.display()));
        assert!(expanded.contains(retained_step), "{expanded}");
        verify_c0_sources(&expanded, &c_sources).unwrap_or_else(|error| {
            panic!(
                "expanded proof from `{}` did not replay independently: {error:?}",
                path.display()
            )
        });

        let without_retained_step = expanded
            .lines()
            .filter(|line| !line.contains(retained_step))
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            verify_c0_sources(&without_retained_step, &c_sources).is_err(),
            "`{}` replayed after deleting its selected retained theorem step",
            path.display()
        );
    }
}

#[test]
fn frame_certified_outcome_claim_closes_on_the_checked_proof() {
    let c_source = r#"
        int32 preserve_after_loop(int32 p[], int32 n) {
            int32 i;
            i = 0;
            while (i < n) {
                p[i] = i;
                i = i + 1;
            }
            return i;
        }
    "#;
    let click_source = r#"
        verifying "preserve.c";

        int32 preserve_after_loop(int32 p[], int32 n) {
            requires n >= 0;
            requires n <= 100;
            requires loadable(p[0..n + 1]);
            consumes p[0..n + 1];
            ensures preserved: p[n] == old(p[n]);
        } by {
            step();
            step();
            loop {
                invariant i >= 0;
                invariant i <= n;
                mutable p[0..n] by frame;
                initialize by simp;
                preserve by {
                    step();
                    step();
                    close_invariants();
                }
            }
            step();
            frame(loop(0));
            simp();
        }
    "#;
    let sources = [("preserve.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the frame-certified ensure should close through Proof");
    let compatibility_events = events
        .iter()
        .take_while(|event| {
            !matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "whole-contract certificate construction"
            )
        })
        .filter(|event| {
            matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "outcome simp legacy exit planning"
            )
        })
        .collect::<Vec<_>>();
    assert!(
        compatibility_events.is_empty(),
        "a checked frame goal must not enter legacy exit planning: {compatibility_events:#?}"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &sources,
        "preserve_after_loop",
        CProofClaim::Grouped,
    )
    .expect("the frame-certified outcome should expand");
    verify_c0_sources(&expanded, &sources)
        .expect("the frame-certified expansion should replay independently");
}

#[test]
fn outcome_simp_transports_loadability_on_the_checked_proof() {
    let summarize_c = r#"
        int32 summarize(int32* p) {
            return 0;
        }
    "#;
    let use_c = r#"
        int32 use_summary(int32* p) {
            int32 result;
            result = summarize(p);
            return result;
        }
    "#;
    let click_source = r#"
        verifying "summarize.c";
        verifying "use_summary.c";

        int32 summarize(int32* p) {
            requires loadable(p[0..1]);
            ensures loadable(p[0..1]);
        } by {
            execute();
            simp();
        }

        int32 use_summary(int32* p) {
            requires loadable(p[0..1]);
            ensures loadable(p[0..1]);
        } by {
            execute();
            simp();
        }
    "#;
    let sources = [("summarize.c", summarize_c), ("use_summary.c", use_c)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the call-preserved loadability should transport through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp compatibility construction"
        )),
        "outcome loadability transport must bypass compatibility construction: {events:#?}"
    );

    let expanded =
        expand_c0_claim_source(click_source, &sources, "use_summary", CProofClaim::Grouped)
            .expect("the retained loadability transport should expand");
    assert!(expanded.contains("transport"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the retained loadability transport should replay independently");
}

#[test]
fn outcome_simp_transports_unchanged_old_equality_on_the_checked_proof() {
    let c_source = r#"
        int32 shifted_loop_effect_preserves_prefix(int32 p[], int32 n) {
            int32 i;
            i = 1;
            while (i < n) {
                p[i] = i;
                i = i + 1;
            }
            return i;
        }
    "#;
    let click_source = r#"
        verifying "shifted.c";

        int32 shifted_loop_effect_preserves_prefix(int32 p[], int32 n) {
            requires n >= 1;
            requires n <= 2147483647;
            requires loadable(p[0..n]);
            consumes p[0..n];
            ensures keeps_first: p[0] == old(p[0]);
            ensures returns_n: result == n;
        } by {
            step();
            step();
            loop {
                invariant i >= 1;
                invariant i <= n;
                mutable (p + 1)[0..n - 1] by frame;
            }
            step();
            simp();
        }
    "#;
    let sources = [("shifted.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the unchanged old equality should transport through Proof");
    let simp_start = events
        .iter()
        .rposition(|event| {
            matches!(
                event,
                crate::instrumentation::VerificationEvent::TacticStarted(tactic)
                    if tactic.claim == "shifted_loop_effect_preserves_prefix.contract"
                        && tactic.tactic_name == "simp"
            )
        })
        .expect("the final smart simp should be instrumented");
    let simp_end = events[simp_start..]
        .iter()
        .position(|event| {
            matches!(
                event,
                crate::instrumentation::VerificationEvent::TacticFinished { tactic, .. }
                    if tactic.claim == "shifted_loop_effect_preserves_prefix.contract"
                        && tactic.tactic_name == "simp"
            )
        })
        .map(|offset| simp_start + offset)
        .expect("the final smart simp should finish");
    assert!(
        events[simp_start..=simp_end].iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp compatibility construction"
        )),
        "outcome old-equality transport must bypass compatibility construction during the final simp: {:#?}",
        &events[simp_start..=simp_end]
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &sources,
        "shifted_loop_effect_preserves_prefix",
        CProofClaim::Grouped,
    )
    .expect("the retained old-equality transport should expand");
    assert!(
        expanded.contains("transport(old(p[0]) == old(p[0]), p[0] == old(p[0])) using {"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &sources)
        .expect("the retained old-equality transport should replay independently");
}

#[test]
fn outcome_simp_instantiates_an_unfolded_byte_predicate_on_the_checked_proof() {
    let c_source = r#"
        int32 byte_prefix(uint8 p[], int32 n) {
            return 0;
        }
    "#;
    let click_source = r#"
        verifying "byte_prefix.c";

        int32 byte_prefix(uint8 p[], int32 n) {
            requires loadable(p[0..3]);
            requires no_y: bytes_all_not_eq(p, 0, 3, 'y');
            ensures p[1] != 'y' by {
                execute();
                unfold(bytes_all_not_eq);
                simp();
            }
        }
    "#;
    let sources = [("byte_prefix.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the unfolded byte universal should instantiate through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp legacy exit planning"
                    || name == "outcome simp compatibility construction"
        )),
        "unfolded universal closure must not enter outcome compatibility planning: {events:#?}"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &sources,
        "byte_prefix",
        CProofClaim::Ensure(0),
    )
    .expect("the retained universal specialization should expand");
    assert!(expanded.contains("instantiate("), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the unfolded universal specialization should replay independently");
}

#[test]
fn outcome_simp_materializes_selected_composite_separation_on_the_checked_proof() {
    let c_source = r#"
        struct owner {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 observe_nested_separate_contains(struct owner* owner) {
            return 0;
        }
    "#;
    let click_source = r#"
        resource backing_buffer(owner: struct owner*) {
            owns owner->data[0..owner->cap];
        }

        resource nested_owned_buffer(owner: struct owner*) {
            owns owner->len;
            owns owner->cap;
            owns owner->data;
            contains backing_buffer(owner);
            fact 0 <= owner->len;
            fact owner->len <= owner->cap;
        }

        verifying "observe.c";

        int32 observe_nested_separate_contains(struct owner* owner) {
            consumes nested_owned_buffer(owner);
            ensures separate(
                memory(owner[0..3]),
                memory(owner->data[0..owner->cap])
            ) by {
                observe(nested_owned_buffer(owner));
                observe(backing_buffer(owner));
                execute();
                simp();
            }
        }
    "#;
    let sources = [("observe.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified
        .expect("the observed composition should certify its selected separation through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp legacy exit planning"
                    || name == "outcome simp compatibility construction"
        )),
        "selected resource separation must not enter outcome compatibility planning: {events:#?}"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &sources,
        "observe_nested_separate_contains",
        CProofClaim::Ensure(0),
    )
    .expect("the retained resource separation should expand");
    assert!(expanded.contains("assumption();"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the selected resource separation should replay independently");
}

#[test]
fn quantified_old_transport_substitutes_its_introduced_binder_on_the_checked_proof() {
    let c_source = r#"
        int32 shifted_copy(int32 dst[], int32 src[], int32 n) {
            int32 i;
            i = 1;
            while (i < n) {
                dst[i] = src[i];
                i = i + 1;
            }
            return i;
        }
    "#;
    let click_source = r#"
        verifying "shifted_copy.c";

        int32 shifted_copy(int32 dst[], int32 src[], int32 n) {
            requires n >= 1;
            requires n <= 2147483647;
            requires loadable(dst[0..n]);
            requires loadable(src[0..n]);
            consumes dst[0..n];
            views src[0..n];
            requires separate(memory(dst[0..n]), memory(src[0..n]));
            ensures forall (k: int32) {
                0 <= k and k < n implies src[k] == old(src[k])
            };
            ensures result == n;
        } by {
            step();
            step();
            loop {
                invariant i >= 1;
                invariant i <= n;
                mutable (dst + 1)[0..n - 1] by frame;
            }
            step();
            simp();
        }
    "#;
    let sources = [("shifted_copy.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the quantified old equality should transport through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp legacy exit planning"
                    || name == "outcome simp compatibility construction"
        )),
        "quantified old transport must not enter outcome compatibility planning: {events:#?}"
    );

    let expanded =
        expand_c0_claim_source(click_source, &sources, "shifted_copy", CProofClaim::Grouped)
            .expect("the retained quantified transport should expand");
    assert!(expanded.contains("intro();"), "{expanded}");
    assert!(expanded.contains("extract(0 <= k);"), "{expanded}");
    assert!(expanded.contains("extract(k < n);"), "{expanded}");
    assert!(
        expanded.contains("transport(old(src[k]) == old(src[k]), src[k] == old(src[k])) using {"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &sources)
        .expect("the quantified old transport should replay independently");
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("the unfold-then-simp have should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "surface certificate replay"
        )),
        "the migrated unfold-then-simp path must retain its checked Proof: {events:#?}"
    );
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
fn selected_post_execution_frame_stays_inside_open_scope() {
    let c_source = r#"
            int32 increment_counted(int32 p[]) {
                p[0] = p[0] + 1;
                return p[0];
            }
        "#;
    let click_source = r#"
            resource counted(p: int32*) {
                owns p[0..1];
                fact p[0] == count(counted(p));
            }

            verifying "increment_counted.c";

            int32 increment_counted(int32 p[]) {
                owns counted(p);
                produces counted(p);
                mutable p[0..1];
            } by {
                open(counted(p)) {
                    execute();
                    frame();
                }
                simp();
            }
        "#;
    let offset = click_source
        .find("frame();")
        .expect("proof should contain the selected frame");
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
        &[("increment_counted.c", c_source)],
        line,
        column,
    )
    .expect("selected frame inside an open scope should expand");
    assert!(!expanded.contains("frame();"), "{expanded}");
    verify_c0_sources(&expanded, &[("increment_counted.c", c_source)])
        .expect("expanded frame must replay before the open scope closes");
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

#[test]
fn pure_pointer_add_zero_simp_expands_to_rewrite_and_assumption() {
    let click_source = r#"
            theorem pointer_add_zero_equals(
                base: int32*,
                offset: int32,
                target: int32*
            ) {
                requires base == target;
                requires offset == 0;

                ensures base + offset == target by {
                    simp();
                }
            }
        "#;
    let offset = click_source.find("simp()").unwrap();
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
        .expect("the pointer-offset identity simp should have an explicit certificate");
    assert!(expanded.contains("rewrite(offset == 0);"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp()"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded pointer identity proof should replay");
}

#[test]
fn pure_branching_disjunction_simp_expands_to_left_right() {
    let click_source = r#"
            theorem int32_sign_split(x: int32) {
                ensures x <= 0 or x > 0 by {
                    if x <= 0 {
                        simp();
                    } else {
                        simp();
                    }
                }
            }
        "#;
    let offset = click_source.find("if x <= 0").unwrap();
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
        .expect("the branching disjunction proof should have an explicit certificate");
    assert!(expanded.contains("left();"), "{expanded}");
    assert!(expanded.contains("right();"), "{expanded}");
    assert!(!expanded.contains("simp()"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded branching disjunction proof should replay");
}

#[test]
fn pure_folded_constant_successor_simp_expands_to_successor_bound() {
    let click_source = r#"
            theorem successor_of_zero_below_bound(x: int32, bound: int32) {
                requires x == 0;
                requires 2 <= bound;

                ensures x + 1 < bound by {
                    simp();
                }
            }
        "#;
    let offset = click_source.find("simp()").unwrap();
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
        .expect("the folded constant successor simp should have an explicit certificate");
    assert!(expanded.contains("rewrite(x == 0);"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_successor_le_implies_lt("),
        "{expanded}"
    );
    assert!(!expanded.contains("simp()"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded constant successor proof should replay");
}

#[test]
fn unfolded_conjunction_have_simp_expands_to_a_split_certificate() {
    let c_source = r#"
            struct pair {
                int32 low;
                int32 high;
            };

            void set_pair(struct pair* pair, int32 bound) {
                pair->low = 0;
                pair->high = bound;
            }
        "#;
    let click_source = r#"
            predicate ordered_pair(pair: struct pair*) {
                0 <= pair->low and pair->low <= pair->high
            }

            verifying "set_pair.c";

            void set_pair(struct pair* pair, int32 bound) {
                requires 0 <= bound;
                owns object(pair);
                mutable pair->low, pair->high;

                ensures ordered_pair(pair);
            } by {
                execute();
                have ordered_pair(pair) by {
                    unfold(ordered_pair);
                    simp();
                }
                frame();
                simp();
            }
        "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("set_pair.c", c_source)])
    });
    verified.expect("the unfolded conjunction should verify on the checked Proof path");
    let source_verification_events = events.iter().take_while(|event| {
        !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "whole-contract certificate construction"
        )
    });
    assert!(
        source_verification_events
            .into_iter()
            .all(|event| !matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "post-execution smart have compatibility construction"
                        || name.starts_with("post-execution simple have replay")
            )),
        "the checked unfold and structural simp must not reconstruct or replay their proof: {events:#?}"
    );
    let offset = click_source.find("have ordered_pair").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("set_pair.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the unfolded conjunction have simp should expand to a split certificate");
    assert!(expanded.contains("split();"), "{expanded}");
    assert!(expanded.contains("have 0 <= pair->low"), "{expanded}");
    assert!(
        expanded.contains("have pair->low <= pair->high"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("set_pair.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "the expanded split certificate should replay: {}\n{expanded}",
            error.message()
        )
    });
}

#[test]
fn outcome_predecessor_bound_simp_expands_to_the_named_rule() {
    let c_source = r#"
            struct pair {
                int32 low;
                int32 high;
            };

            void drop_one(struct pair* pair) {
                pair->low = pair->low - 1;
            }
        "#;
    let click_source = r#"
            predicate ordered_pair(pair: struct pair*) {
                0 <= pair->low and pair->low <= pair->high
            }

            verifying "drop_one.c";

            void drop_one(struct pair* pair) {
                requires ordered_pair(pair);
                requires pair->low == 1;
                owns object(pair);
                mutable pair->low;

                ensures ordered_pair(pair);
            } by {
                unfold(ordered_pair);
                execute();
                frame();
                simp();
            }
        "#;
    let offset = click_source.rfind("simp()").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("drop_one.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the predecessor bound simp should expand to the named rule");
    assert!(expanded.contains("split();"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_nonnegative_predecessor_upper_bound("),
        "{expanded}"
    );
    assert!(!expanded.contains("simp()"), "{expanded}");
    verify_c0_sources(&expanded, &[("drop_one.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "the expanded predecessor bound certificate should replay: {}\n{expanded}",
            error.message()
        )
    });
}
