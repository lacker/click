use super::*;

#[test]
fn frontier_local_loop_verifies_and_advances_to_exit() {
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
                loop as count {
                    invariant i >= 0;
                    invariant i <= 3;
                    initialize by simp;
                    preserve by {
                        step();
                        close_invariants();
                    }
                }
                have at(count.entry, i) == 0 by simp;
                have at(count.exit, i) == 3 by simp;
                step();
                simp();
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
        .expect("frontier-local loop proof should verify from its actual entry frontier");

    assert_eq!(verified.len(), 1);
}

#[test]
fn loop_initialization_theorem_search_retains_checked_point_proof() {
    let c_source = r#"
            int32 initialize_with_theorem(int32 x) {
                while (x < 1) {
                    x = 0;
                }
                return x;
            }
        "#;
    let click_source = r#"
            verifying "initialize_with_theorem.c";

            predicate acceptable(x: int32) {
                x >= 0
            }

            theorem nonnegative_is_acceptable(x: int32) {
                requires x >= 0;
                ensures acceptable(x) by {
                    unfold(acceptable);
                    simp();
                }
            }

            int32 initialize_with_theorem(int32 x) {
                requires x >= 0;
                ensures acceptable(result);
            } by {
                loop {
                    invariant acceptable(x);
                    initialize by {
                        apply(nonnegative_is_acceptable(x));
                        simp();
                    }
                    preserve by {
                        step();
                        apply(nonnegative_is_acceptable(x));
                        simp();
                    }
                }
                step();
                unfold(acceptable);
                simp();
            }
        "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("initialize_with_theorem.c", c_source)])
    });
    verified.expect("loop initialization theorem search should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim.contains("loop(0).initialize")
                    && name == "surface certificate replay"
        )),
        "the checked initialization Proof must not be independently replayed: {events:#?}"
    );

    let offset = click_source
        .find("apply(nonnegative_is_acceptable(x));")
        .expect("initialization proof should contain its smart theorem application");
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
        &[("initialize_with_theorem.c", c_source)],
        line,
        column,
    )
    .expect("the retained initialization theorem step should expand");
    assert!(
        expanded.contains("apply(nonnegative_is_acceptable(x)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("x >= 0;"), "{expanded}");
    verify_c0_sources(&expanded, &[("initialize_with_theorem.c", c_source)])
        .expect("expanded initialization theorem application should independently verify");
}

#[test]
fn loop_initialization_simp_retains_checked_point_proof() {
    let c_source = r#"
            int32 initialize_by_simp(int32 x) {
                while (x < 1) {
                    x = 0;
                }
                return x;
            }
        "#;
    let click_source = r#"
            verifying "initialize_by_simp.c";

            int32 initialize_by_simp(int32 x) {
                requires x >= 0;
                ensures result >= 0;
            } by {
                loop {
                    invariant x >= 0;
                    initialize by simp;
                    preserve by {
                        step();
                        close_invariants();
                    }
                }
                step();
                simp();
            }
        "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("initialize_by_simp.c", c_source)])
    });
    verified.expect("loop initialization simp should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim.contains("loop(0).initialize")
                    && name == "surface certificate replay"
        )),
        "the checked initialization simp must not be independently replayed: {events:#?}"
    );

    let offset = click_source
        .find("initialize by simp")
        .expect("initialization proof should contain its smart simp")
        + "initialize by ".len();
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
        &[("initialize_by_simp.c", c_source)],
        line,
        column,
    )
    .expect("the retained initialization closer should expand");
    assert!(!expanded.contains("initialize by simp"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    verify_c0_sources(&expanded, &[("initialize_by_simp.c", c_source)])
        .expect("expanded initialization closer should independently verify");
}

#[test]
fn frontier_local_loop_rejects_a_non_loop_frontier() {
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
                loop {
                    invariant i >= 0;
                }
            }
        "#;

    let error = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
        .expect_err("loop should not seek forward from a non-loop frontier");

    assert!(
        error
            .message()
            .contains("requires the execution frontier to be at a loop"),
        "{}",
        error.message()
    );
    assert!(
        error.message().contains("statement(0)"),
        "{}",
        error.message()
    );
}

#[test]
fn frontier_loop_initialization_rejects_execution_tactics() {
    let c_source = r#"
            int32 count_once() {
                int32 i;
                i = 0;
                while (i < 1) {
                    i = i + 1;
                }
                return i;
            }
        "#;
    let click_source = r#"
            verifying "count_once.c";

            int32 count_once() {
                ensures result == 1;
            } by {
                step();
                step();
                loop {
                    invariant i >= 0;
                    initialize by {
                        step();
                    }
                }
            }
        "#;

    let error = verify_c0_sources(click_source, &[("count_once.c", c_source)])
        .expect_err("initialization should not execute C statements");
    assert!(
        error.message().contains("`initialize`")
            && error.message().contains("pure proof")
            && error.message().contains("step"),
        "{}",
        error.message()
    );
}

#[test]
fn frontier_loop_preservation_requires_one_complete_iteration() {
    let c_source = r#"
            int32 count_once() {
                int32 i;
                i = 0;
                while (i < 1) {
                    i = i + 1;
                    i = i;
                }
                return i;
            }
        "#;
    let click_source = r#"
            verifying "count_once.c";

            int32 count_once() {
                ensures result == 1;
            } by {
                step();
                step();
                loop {
                    invariant i >= 0;
                    preserve by {
                        step();
                    }
                }
            }
        "#;

    let error = verify_c0_sources(click_source, &[("count_once.c", c_source)])
        .expect_err("preservation should traverse the complete loop body");
    assert!(
        error
            .message()
            .contains("must execute exactly one complete loop-body iteration"),
        "{}",
        error.message()
    );
}

#[test]
fn frontier_local_loop_resolves_composite_resources_in_nested_proofs() {
    let click_source = r#"
            resource box_value(owner: struct box*) {
                owns owner->value;
            }

            verifying "count_once.c";

            int32 count_once(struct box* owner) {
                owns box_value(owner);
                ensures result == 1;
            } by {
                step();
                step();
                loop {
                    invariant i >= 0;
                    invariant i <= 1;
                    mutable owner->value by {
                        observe(box_value(owner));
                        frame() using {};
                    }
                    initialize by simp;
                    preserve by {
                        observe(box_value(owner));
                        step();
                        close_invariants();
                    }
                }
                step();
                simp();
            }
        "#;

    let parsed = parser::parse_file_items(click_source).expect("source should parse");
    let expanded = validation::expand_declared_resource_clauses(parsed)
        .expect("nested loop resources should resolve");
    let loop_clause = expanded.function_blocks()[0]
        .grouped_proof()
        .and_then(SourceProof::tactics)
        .and_then(|tactics| {
            tactics.iter().find_map(|tactic| match tactic {
                ProofTactic::Loop(clause) => Some(clause),
                _ => None,
            })
        })
        .expect("grouped proof should contain a loop tactic");

    let effect_observe = loop_clause.items()[2]
        .proof()
        .tactics()
        .and_then(|tactics| tactics.first())
        .expect("effect should contain an observe tactic");
    let preserve_observe = loop_clause
        .preserve_proof()
        .and_then(SourceProof::tactics)
        .and_then(|tactics| tactics.first())
        .expect("preservation should contain an observe tactic");
    for tactic in [effect_observe, preserve_observe] {
        assert!(matches!(
            tactic,
            ProofTactic::ObserveResource(ResourceClause::Declared {
                kind: ResourceKind::Composite,
                parameter_types,
                ..
            }) if parameter_types == &[C0Type::Int32Pointer]
        ));
    }
}

#[test]
fn frontier_local_loop_frames_untouched_composite_pointer_field_across_call() {
    let callee_c = r#"
            struct holder {
                int32 value;
                int32* data;
            };

            int32 mutate(struct holder* owner) {
                owner->value = 0;
                owner->data[0] = 0;
                return 0;
            }
        "#;
    let caller_c = r#"
            struct holder {
                int32 value;
                int32* data;
            };

            int32 call_once(struct holder* owner) {
                int32 i;
                i = 0;
                while (i < 1) {
                    mutate(owner);
                    i = i + 1;
                }
                return i;
            }
        "#;
    let click_source = r#"
            resource holder(owner: struct holder*) {
                owns owner->value;
                owns owner->data;
                owns owner->data[0..1];
                fact separate(memory(object(owner)), memory(owner->data[0..1]));
            }

            verifying "mutate.c";
            verifying "call_once.c";

            int32 mutate(struct holder* owner) {
                owns holder(owner);
                mutable owner->value, owner->data[0..1];
            } by {
                unfold(holder(owner));
                execute();
                fold(holder(owner));
                frame();
                simp();
            }

            int32 call_once(struct holder* owner) {
                owns holder(owner);
                mutable owner->value, owner->data[0..1];
                ensures result == 1;
            } by {
                step();
                step();
                loop {
                    invariant i >= 0;
                    invariant i <= 1;
                    mutable owner->value, owner->data[0..1] by {
                        frame() using {
                            separate(memory(object(owner)), memory(owner->data[0..1]));
                        }
                    }
                    initialize by simp;
                    preserve by {
                        step() using {};
                        step() using {
                            i < 1;
                        }
                        close_invariants();
                    }
                }
                step();
                frame();
                simp();
            }
        "#;

    let sources = [("mutate.c", callee_c), ("call_once.c", caller_c)];
    verify_c0_sources(click_source, &sources)
        .expect("the opaque call effect should preserve the untouched pointer field");

    let initialization = click_source
        .find("initialize by simp")
        .expect("loop initialization should have a source position")
        + "initialize by ".len();
    let position = expansion::position_at_offset(click_source, initialization);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("frontier-loop expansion should retain the loop body's callee contract");
    verify_c0_sources(&expanded, &sources)
        .expect("expanded frontier-loop initialization should replay");
}

#[test]
fn frontier_local_loop_verifies_a_lowered_c_for_loop() {
    let c_source = r#"
            int32 count_to_three() {
                int32 i;
                for (i = 0; i < 3; i = i + 1) {
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
                loop {
                    invariant i >= 0;
                    invariant i <= 3;
                    initialize by simp;
                    preserve by {
                        step();
                        step();
                        close_invariants();
                    }
                }
                step();
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
        .expect("frontier-local loop should bind a C `for` lowered to a kernel loop");
}

#[test]
fn frontier_local_loop_verifies_at_a_branch_local_frontier() {
    let c_source = r#"
            int32 branch_count(int32 flag) {
                int32 i;
                i = 0;
                if (flag) {
                    while (i < 2) {
                        i = i + 1;
                    }
                } else {
                    i = 1;
                }
                return i;
            }
        "#;
    let click_source = r#"
            verifying "branch_count.c";

            int32 branch_count(int32 flag) {
                ensures result >= 1;
                ensures result <= 2;
            } by {
                step();
                step();
                if flag != 0 {
                    step();
                    loop {
                        invariant i >= 0;
                        invariant i <= 2;
                        initialize by simp;
                        preserve by {
                            step();
                            close_invariants();
                        }
                    }
                } else {
                    step();
                    step();
                }
                step();
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("branch_count.c", c_source)])
        .expect("frontier-local loop should use the branch's actual execution context");
}

#[test]
fn frontier_local_loop_verifies_nested_loops_at_their_respective_frontiers() {
    let c_source = r#"
            int32 nested_count() {
                int32 i;
                int32 j;
                i = 0;
                while (i < 2) {
                    j = 0;
                    while (j < 2) {
                        j = j + 1;
                    }
                    i = i + 1;
                }
                return i;
            }
        "#;
    let click_source = r#"
            verifying "nested_count.c";

            int32 nested_count() {
                ensures result == 2;
            } by {
                step();
                step();
                step();
                loop {
                    invariant i >= 0;
                    invariant i <= 2;
                    initialize by simp;
                    preserve by {
                        step();
                        loop {
                            invariant j >= 0;
                            invariant j <= 2;
                            initialize by simp;
                            preserve by {
                                step();
                                close_invariants();
                            }
                        }
                        step();
                        close_invariants();
                    }
                }
                step();
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("nested_count.c", c_source)])
        .expect("nested loop proofs should be scoped to their respective frontiers");
}

#[test]
fn frontier_local_loop_verifies_step_relative_mutable_effects() {
    let c_source = r#"
            int32 fill_n(int32 p[], int32 n) {
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
            verifying "fill_n.c";

            int32 fill_n(int32 p[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires loadable(p[0..n]);
                consumes p[0..n];
                ensures result == n;
            } by {
                step();
                step();
                loop {
                    invariant i >= 0;
                    invariant i <= n;
                    step {
                        mutable p[i..i + 1] by frame;
                    }
                    initialize by simp;
                    preserve by {
                        step();
                        step();
                        close_invariants();
                    }
                }
                step();
                simp();
            }
        "#;

    crate::instrumentation::with_deadline(std::time::Duration::from_secs(3), || {
        verify_c0_sources(click_source, &[("fill_n.c", c_source)])
    })
    .expect("frontier-local loops should certify step-relative mutable effects");
}

#[test]
fn frontier_loop_step_expansion_uses_the_current_invariant_lowering() {
    let c_source = r#"
            int32 fill_n(int32 p[], int32 n) {
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
            verifying "fill_n.c";

            int32 fill_n(int32 p[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires loadable(p[0..n]);
                consumes p[0..n];
                ensures result == n;
            } by {
                step();
                step();
                loop {
                    invariant i >= 0 and i <= n;
                    mutable p[0..n] by frame;
                    initialize by simp;
                    preserve by {
                        step();
                        step();
                        close_invariants();
                    }
                }
                step();
                simp();
            }
        "#;
    let preserve_step = click_source
        .find("preserve by {")
        .and_then(|offset| {
            click_source[offset..]
                .find("step();")
                .map(|step| offset + step)
        })
        .expect("proof should contain a preservation step");
    let line = click_source[..preserve_step]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = preserve_step
        - click_source[..preserve_step]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("fill_n.c", c_source)], line, column)
            .expect("the preservation store should expand");

    assert_ne!(expanded, click_source);
    verify_c0_sources(&expanded, &[("fill_n.c", c_source)])
        .expect("the expanded store should use the invariant at the current frontier");
}

#[test]
fn frontier_local_loop_preserves_a_perpetual_partial_contract() {
    let c_source = r#"
            int32 spin() {
                while (1) {
                }
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "spin.c";

            int32 spin() {
                ensures 0 == 0;
            } by {
                loop {
                    invariant 0 == 0;
                    initialize by simp;
                    preserve by {
                        step();
                        close_invariants();
                    }
                }
                simp();
            }
        "#;

    crate::instrumentation::with_deadline(std::time::Duration::from_secs(3), || {
        verify_c0_sources(click_source, &[("spin.c", c_source)])
    })
    .expect("a frontier-local loop without `decreases` should prove partial correctness");
}

#[test]
fn frontier_local_perpetual_loop_expands_a_direct_closer_without_a_return() {
    let c_source = r#"
            int32 spin() {
                while (1) {
                }
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "spin.c";

            int32 spin() {
                ensures 0 == 0;
            } by {
                loop {
                    invariant 0 == 0;
                    initialize by simp;
                    preserve by {
                        step();
                        close_invariants();
                    }
                }
                simp();
            }
        "#;
    let closer = click_source
        .rfind("simp();")
        .expect("proof should contain its direct closer");
    let line = click_source[..closer]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = closer
        - click_source[..closer]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[("spin.c", c_source)], line, column)
        .expect("a direct tautology closer should expand without a return outcome");

    verify_c0_sources(&expanded, &[("spin.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "the expanded perpetual-loop proof should freshly replay: {}\n{expanded}",
            error.message()
        )
    });
}

#[test]
fn frontier_local_loop_checks_an_optional_decreases_measure() {
    let c_source = r#"
            int32 drain(int32 n) {
                while (n > 0) {
                    n = n - 1;
                }
                return n;
            }
        "#;
    let click_source = r#"
            verifying "drain.c";

            int32 drain(int32 n) {
                requires n >= 0;
                ensures result == 0;
            } by {
                loop {
                    decreases n;
                    invariant n >= 0;
                    initialize by simp;
                    preserve by {
                        step();
                        close_invariants();
                    }
                }
                step();
                simp();
            }
        "#;

    let (session, _) = C0VerificationSession::new(click_source, &[("drain.c", c_source)])
        .expect("frontier-local loop should retain structural termination checking");
    assert!(session.function_termination_is_verified("drain"));
}

#[test]
fn frontier_local_loop_keyword_expands_omitted_phases() {
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
                    invariant i >= 0;
                    invariant i <= n;
                }
                step();
                simp();
            }
        "#;
    let loop_offset = click_source
        .find("loop {")
        .expect("proof should contain its loop keyword");
    let line = click_source[..loop_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = loop_offset
        - click_source[..loop_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("count_to_n.c", c_source)], line, column)
            .expect("the loop keyword should expand all omitted phase automation");

    assert!(expanded.contains("initialize by {"), "{expanded}");
    assert!(expanded.contains("preserve by {"), "{expanded}");
    verify_c0_sources(&expanded, &[("count_to_n.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "the expanded frontier-local loop should freshly replay: {}\n{expanded}",
            error.message()
        )
    });
}

#[test]
fn loop_exit_simp_expands_invariant_conjuncts_explicitly() {
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
                ensures result == n and result >= 0;
            } by {
                step();
                step();
                loop {
                    invariant i >= 0 and i <= n;
                }
                step();
                simp();
            }
        "#;
    let simp_offset = click_source
        .rfind("simp();")
        .expect("proof should contain its final simp");
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
        expand_c0_tactic_source_at(click_source, &[("count_to_n.c", c_source)], line, column)
            .expect("loop-exit simp should expand through explicit invariant conjuncts");

    assert!(
        expanded.contains("at(loop(0).exit, i) <= at(loop(0).exit, n);"),
        "{expanded}"
    );
    assert!(
        expanded.contains("not at(loop(0).exit, i) < at(loop(0).exit, n);"),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_le_and_not_lt_implies_eq("),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("count_to_n.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "the expanded loop-exit proof should freshly replay: {}\n{expanded}",
            error.message()
        )
    });
}

#[test]
fn frontier_local_loop_does_not_leak_phase_tactics_into_a_later_expansion() {
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
                loop {
                    invariant i >= 0;
                    invariant i <= 3;
                }
                step();
                simp();
            }
        "#;
    let post_loop_step = click_source
        .rfind("step();")
        .expect("proof should contain a post-loop step");
    let line = click_source[..post_loop_step]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = post_loop_step
        - click_source[..post_loop_step]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("count_to_three.c", c_source)],
        line,
        column,
    )
    .expect("the post-loop step should expand independently");

    verify_c0_sources(&expanded, &[("count_to_three.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "post-loop expansion should not leak loop-region tactics: {}\n{expanded}",
            error.message()
        )
    });
}

#[test]
fn frontier_local_loop_expands_an_explicit_nested_tactic_at_its_own_location() {
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
                loop {
                    invariant i >= 0;
                    invariant i <= 3;
                    initialize by simp;
                    preserve by {
                        step();
                        close_invariants();
                    }
                }
                step();
                simp();
            }
        "#;
    let initialize_simp = click_source
        .find("initialize by simp")
        .expect("proof should contain explicit initialization")
        + "initialize by ".len();
    let line = click_source[..initialize_simp]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = initialize_simp
        - click_source[..initialize_simp]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let inventory = c0_smart_tactic_source_sites(click_source, &[("count_to_three.c", c_source)])
        .expect("frontier-local nested tactics should be inventoried without verification");
    let matching_inventory = inventory
        .iter()
        .filter(|site| {
            c0_tactic_source_position(
                click_source,
                &[("count_to_three.c", c_source)],
                &site.claim_label,
                site.source_index,
            )
            .is_ok_and(|position| position.line == line && position.column == column)
        })
        .collect::<Vec<_>>();
    assert_eq!(matching_inventory.len(), 1, "{inventory:?}");
    assert_eq!(matching_inventory[0].tactic_name, "simp");

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("count_to_three.c", c_source)],
        line,
        column,
    )
    .expect("explicit initialization tactic should expand at its own source location");

    assert!(!expanded.contains("initialize by simp"), "{expanded}");
    assert!(expanded.contains("preserve by {"), "{expanded}");
    verify_c0_sources(&expanded, &[("count_to_three.c", c_source)])
        .expect("expanded explicit initialization tactic should freshly replay");
}

#[test]
fn frontier_local_loop_at_function_entry_keeps_initialization_capture_separate() {
    let c_source = r#"
            int32 drain(int32 n) {
                while (n > 0) {
                    n = n - 1;
                }
                return n;
            }
        "#;
    let click_source = r#"
            verifying "drain.c";

            int32 drain(int32 n) {
                requires n >= 0;
                ensures result == 0;
            } by {
                loop {
                    decreases n;
                    invariant n >= 0;
                    initialize by simp;
                    preserve by {
                        step();
                        close_invariants();
                    }
                }
                step();
                simp();
            }
        "#;

    let tactics = super::proof::capture_c0_tactic_expansion(
        click_source,
        &[("drain.c", c_source)],
        super::expansion::ProofSite::FunctionClaim {
            function_name: "drain".to_string(),
            claim: CProofClaim::Grouped,
        },
        1,
    )
    .expect("initialization should retain its own expansion certificate");

    assert!(
        !tactics
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::CloseInvariants)),
        "initialization captured preservation tactics: {tactics:?}"
    );
}

#[test]
fn frontier_local_loop_expands_a_tactic_inside_preservation_at_its_own_location() {
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
                loop {
                    invariant i >= 0;
                    invariant i <= 3;
                    initialize by simp;
                    preserve by {
                        step();
                        close_invariants();
                    }
                }
                step();
                simp();
            }
        "#;
    let preserve_step = click_source
        .find("preserve by {")
        .and_then(|offset| {
            click_source[offset..]
                .find("step();")
                .map(|step| offset + step)
        })
        .expect("proof should contain a preservation step");
    let line = click_source[..preserve_step]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = preserve_step
        - click_source[..preserve_step]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("count_to_three.c", c_source)],
        line,
        column,
    )
    .expect("preservation step should expand at its own source location");

    assert_ne!(expanded, click_source);
    assert!(expanded.contains("initialize by simp"), "{expanded}");
    verify_c0_sources(&expanded, &[("count_to_three.c", c_source)])
        .expect("expanded preservation step should freshly replay");
}

#[test]
fn frontier_local_loop_expands_an_explicit_effect_tactic_at_its_own_location() {
    let c_source = r#"
            int32 fill(int32 p[], int32 n) {
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
            verifying "fill.c";

            int32 fill(int32 p[], int32 n) {
                requires n >= 0 and n <= 2147483647;
                requires loadable(p[0..n]);
                consumes p[0..n];
                ensures result == n;
            } by {
                step();
                step();
                loop {
                    invariant i >= 0;
                    invariant i <= n;
                    step {
                        mutable p[i..i + 1] by frame;
                    }
                }
                step();
                simp();
            }
        "#;
    let effect_frame = click_source
        .find("mutable p[i..i + 1] by frame")
        .expect("proof should contain an explicit effect tactic")
        + "mutable p[i..i + 1] by ".len();
    let line = click_source[..effect_frame]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = effect_frame
        - click_source[..effect_frame]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[("fill.c", c_source)], line, column)
        .expect("the explicit effect tactic should expand at its own source location");

    assert!(
        !expanded.contains("mutable p[i..i + 1] by frame"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("fill.c", c_source)])
        .expect("expanded explicit effect tactic should freshly replay");
}

#[test]
fn frontier_effect_expansion_ignores_generated_preservation_suffix() {
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

            predicate bounded(i: int32) {
                i >= 0 and i <= 3
            }

            int32 count_to_three() {
                ensures result == 3;
            } by {
                step();
                step();
                loop {
                    invariant bounded(i);
                    immutable by frame;
                    initialize by {
                        unfold(bounded);
                        simp();
                    }
                    preserve by {
                        unfold(bounded);
                    }
                }
                step();
                simp();
            }
        "#;
    let effect_frame = click_source
        .find("immutable by frame")
        .expect("proof should contain an explicit effect tactic")
        + "immutable by ".len();
    let line = click_source[..effect_frame]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = effect_frame
        - click_source[..effect_frame]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("count_to_three.c", c_source)],
        line,
        column,
    )
    .expect("the effect frame should expand instead of a generated preservation step");

    assert!(!expanded.contains("immutable by frame"), "{expanded}");
    assert!(expanded.contains("frame() using"), "{expanded}");
    verify_c0_sources(&expanded, &[("count_to_three.c", c_source)])
        .expect("expanded effect certificate should freshly replay");
}

#[test]
fn loop_structural_effect_frame_stays_on_proof() {
    let c_source = r#"
            int32 count_once(int32* p) {
                int32 i;
                i = 0;
                while (i < 1) {
                    i = i + 1;
                }
                return i;
            }
        "#;
    let with_effect = r#"
            verifying "count_once.c";

            int32 count_once(int32* p) {
                requires loadable(p[0..1]);
                ensures result == 1;
            } by {
                step();
                step();
                loop {
                    invariant i >= 0;
                    invariant i <= 1;
                    immutable by frame;
                    initialize by simp;
                    preserve by {
                        step();
                        close_invariants();
                    }
                }
                step();
                simp();
            }
        "#;
    let without_effect = with_effect.replace("                    immutable by frame;\n", "");

    let (baseline, baseline_replays) = proof::count_internal_proof_executions(|| {
        verify_c0_sources(&without_effect, &[("count_once.c", c_source)])
    });
    baseline.expect("the comparison loop without an effect should verify");
    let (verified, effect_replays) = proof::count_internal_proof_executions(|| {
        verify_c0_sources(with_effect, &[("count_once.c", c_source)])
    });
    verified.expect("the loop structural effect should verify");
    assert_eq!(
        effect_replays, baseline_replays,
        "the structural effect added compatibility replay"
    );

    let effect_offset = with_effect
        .find("immutable by frame")
        .expect("the effect proof should have a source position")
        + "immutable by ".len();
    let position = expansion::position_at_offset(with_effect, effect_offset);
    let (expanded, expansion_replays) = proof::count_internal_proof_executions(|| {
        expand_c0_tactic_source_at(
            with_effect,
            &[("count_once.c", c_source)],
            position.line,
            position.column,
        )
    });
    let expanded = expanded.expect("the checked loop effect frame should expand");
    assert!(expanded.contains("frame() using"), "{expanded}");
    assert_eq!(
        expansion_replays, baseline_replays,
        "effect expansion added compatibility replay"
    );

    let (reverified, rewritten_replays) = proof::count_internal_proof_executions(|| {
        verify_c0_sources(&expanded, &[("count_once.c", c_source)])
    });
    reverified.expect("the extracted loop effect should verify normally");
    assert_eq!(
        rewritten_replays, baseline_replays,
        "the rewritten effect added compatibility replay"
    );

    let frame_start = expanded
        .find("frame() using {")
        .expect("the expanded effect should contain a frame");
    let frame_end = expanded[frame_start..]
        .find("\n                        }")
        .map(|offset| frame_start + offset)
        .expect("the expanded frame should have a closing brace");
    let mut corrupted = expanded.clone();
    corrupted.replace_range(
        frame_start + "frame() using {".len()..frame_end,
        "\n                            0 == 1;",
    );
    let (error, corrupted_replays) = proof::count_internal_proof_executions(|| {
        verify_c0_sources(&corrupted, &[("count_once.c", c_source)])
            .expect_err("an unavailable loop-effect frame premise must be rejected")
    });
    assert!(
        error
            .message()
            .contains("requires an exact available premise"),
        "{}",
        error.message()
    );
    assert!(
        corrupted_replays <= baseline_replays,
        "the invalid checked effect entered additional compatibility replay: baseline {baseline_replays}, invalid {corrupted_replays}"
    );
}

#[test]
fn smart_mutable_loop_frame_extracts_exact_proof_premises() {
    let c_source = r#"
            int32 fill_one(int32 p[]) {
                int32 i;
                i = 0;
                while (i < 1) {
                    p[i] = 1;
                    i = i + 1;
                }
                return i;
            }
        "#;
    let with_effect = r#"
            verifying "fill_one.c";

            int32 fill_one(int32 p[]) {
                requires loadable(p[0..1]);
                consumes p[0..1];
                ensures result == 1;
            } by {
                step();
                step();
                loop {
                    invariant i >= 0;
                    invariant i <= 1;
                    mutable p[0..1] by frame;
                    initialize by simp;
                    preserve by {
                        step();
                        step();
                        close_invariants();
                    }
                }
                step();
                simp();
            }
        "#;
    let without_effect = with_effect.replace("                    mutable p[0..1] by frame;\n", "");

    let (baseline, baseline_replays) = proof::count_internal_proof_executions(|| {
        verify_c0_sources(&without_effect, &[("fill_one.c", c_source)])
    });
    baseline.expect("the comparison loop without an effect should verify");
    let (verified, effect_replays) = proof::count_internal_proof_executions(|| {
        verify_c0_sources(with_effect, &[("fill_one.c", c_source)])
    });
    verified.expect("the smart mutable loop frame should verify");
    assert_eq!(
        effect_replays, baseline_replays,
        "smart mutable framing added compatibility replay"
    );

    let offset = with_effect
        .find("mutable p[0..1] by frame")
        .expect("the mutable effect should have a source position")
        + "mutable p[0..1] by ".len();
    let position = expansion::position_at_offset(with_effect, offset);
    let (expanded, expansion_replays) = proof::count_internal_proof_executions(|| {
        expand_c0_tactic_source_at(
            with_effect,
            &[("fill_one.c", c_source)],
            position.line,
            position.column,
        )
    });
    let expanded = expanded.expect("the smart mutable frame should expand");
    let frame_start = expanded
        .find("frame() using {")
        .expect("the expansion should contain an explicit frame");
    let frame_end = expanded[frame_start..]
        .find("\n                        }")
        .map(|offset| frame_start + offset)
        .expect("the expanded frame should have a closing brace");
    assert!(
        expanded[frame_start..frame_end].contains(';'),
        "the smart frame did not expose its checked premises: {expanded}"
    );
    assert_eq!(
        expansion_replays, baseline_replays,
        "smart mutable expansion added compatibility replay"
    );

    let (reverified, rewritten_replays) = proof::count_internal_proof_executions(|| {
        verify_c0_sources(&expanded, &[("fill_one.c", c_source)])
    });
    reverified.expect("the explicit mutable frame should verify normally");
    assert_eq!(
        rewritten_replays, baseline_replays,
        "the rewritten mutable frame added compatibility replay"
    );

    let mut corrupted = expanded.clone();
    corrupted.replace_range(frame_start + "frame() using {".len()..frame_end, "");
    let (error, corrupted_replays) = proof::count_internal_proof_executions(|| {
        verify_c0_sources(&corrupted, &[("fill_one.c", c_source)])
            .expect_err("removing the selected mutable-frame premises must fail")
    });
    assert!(
        error.message().contains("loop effect fact"),
        "{}",
        error.message()
    );
    assert!(
        corrupted_replays <= baseline_replays,
        "the corrupted mutable frame entered additional replay: baseline {baseline_replays}, invalid {corrupted_replays}"
    );
}

#[test]
fn explicit_loop_closer_cannot_bypass_proof_owned_bundle_check() {
    let c_source = r#"
            int32 overshoot() {
                int32 i;
                i = 0;
                while (i < 1) {
                    i = i + 2;
                }
                return i;
            }
        "#;
    let click_source = r#"
            verifying "overshoot.c";

            int32 overshoot() {
                ensures result == 2;
            } by {
                step();
                step();
                loop {
                    invariant i >= 0;
                    invariant i <= 1;
                    initialize by simp;
                    preserve by {
                        step();
                        close_invariants();
                    }
                }
                step();
                simp();
            }
        "#;

    let error = verify_c0_sources(click_source, &[("overshoot.c", c_source)])
        .expect_err("the explicit closer must not authorize a false invariant bundle");
    assert!(
        error.message().contains("invariant bundle") && error.message().contains("preservation"),
        "{}",
        error.message()
    );
}

#[test]
fn branch_shaped_loop_effect_certificate_stays_on_proof() {
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
    let with_effect = r#"
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
    let without_effect = with_effect.replace("                    mutable p[0..3] by frame;\n", "");
    let sources = [("bubble_pass3.c", c_source)];

    let (baseline, baseline_replays) =
        proof::count_internal_proof_executions(|| verify_c0_sources(&without_effect, &sources));
    baseline.expect("the comparison branching loop without an effect should verify");
    assert_eq!(
        baseline_replays, 40,
        "the checked branching preservation path was replayed as a detached certificate"
    );

    let (verified, effect_replays) =
        proof::count_internal_proof_executions(|| verify_c0_sources(with_effect, &sources));
    verified.expect("the branch-shaped smart frame should verify");
    assert_eq!(
        effect_replays, baseline_replays,
        "the branch-shaped smart effect entered compatibility replay"
    );

    let offset = with_effect
        .find("mutable p[0..3] by frame")
        .expect("the mutable effect should have a source position")
        + "mutable p[0..3] by ".len();
    let position = expansion::position_at_offset(with_effect, offset);
    let (expanded, expansion_replays) = proof::count_internal_proof_executions(|| {
        expand_c0_tactic_source_at(with_effect, &sources, position.line, position.column)
    });
    let expanded = expanded.expect("the branch-shaped smart frame should expand");
    assert_eq!(
        expansion_replays, baseline_replays,
        "expanding the branch-shaped smart effect entered compatibility replay"
    );
    assert!(expanded.contains("if p[(j + 1)] < p[j]"), "{expanded}");

    let (reverified, replays) =
        proof::count_internal_proof_executions(|| verify_c0_sources(&expanded, &sources));
    reverified.expect("the branch-shaped explicit frame should verify normally");
    assert_eq!(
        replays, baseline_replays,
        "the branch-shaped structural effect entered compatibility replay"
    );
}

#[test]
fn frame_loop_region_uses_frontier_loop_effect_summary_for_ensures() {
    // `frame(loop(N))` in an ensures-only proof certifies memory-preservation
    // goals from the loop's `mutable` effect summary.  With a symbolic loop
    // bound the closing `simp` cannot certify `p[n] == old(p[n])` on its own,
    // so the qualified frame is load-bearing here.
    let c_source = r#"
            int32 fill_n(int32 p[], int32 n) {
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
            verifying "fill_n.c";

            int32 fill_n(int32 p[], int32 n) {
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

    let (verified, events) = crate::instrumentation::collect(|| {
        crate::instrumentation::with_deadline(std::time::Duration::from_secs(3), || {
            verify_c0_sources(click_source, &[("fill_n.c", c_source)])
        })
    });
    let verified =
        verified.expect("a qualified frame should prove preservation from the loop effect summary");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "fill_n.contract"
                    && name == "smart tactic compatibility replay (tactic 4, source 6)"
        )),
        "the qualified frame's checked Proof successor must bypass compatibility replay: {events:#?}"
    );
    assert!(
        verified[0]
            .expanded_proof_tactics()
            .expect("the qualified frame should retain a surface certificate")
            .iter()
            .any(|tactic| matches!(
                tactic,
                ProofTactic::FrameUsing {
                    region: Some(CodeRegionRef::Loop(0)),
                    premises,
                } if premises.is_empty()
            )),
        "the Proof-owned region frame must retain its exact simple step"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &[("fill_n.c", c_source)],
        "fill_n",
        CProofClaim::Grouped,
    )
    .expect("the Proof-owned qualified frame should expand");
    verify_c0_sources(&expanded, &[("fill_n.c", c_source)])
        .expect("the retained qualified frame should independently reverify");
}

#[test]
fn qualified_frame_with_explicit_premise_advances_through_proof() {
    let c_source = r#"
            int32 fill_n(int32 p[], int32 n) {
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
            verifying "fill_n.c";

            int32 fill_n(int32 p[], int32 n) {
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
                frame(loop(0)) using {
                    n >= 0;
                }
                simp();
            }
        "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        crate::instrumentation::with_deadline(std::time::Duration::from_secs(3), || {
            verify_c0_sources(click_source, &[("fill_n.c", c_source)])
        })
    });
    let verified = verified.expect("an explicit qualified frame premise should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "fill_n.contract"
                    && name == "smart tactic compatibility replay (tactic 4, source 6)"
        )),
        "the premise-bearing qualified frame must bypass compatibility replay: {events:#?}"
    );
    assert!(
        verified[0]
            .expanded_proof_tactics()
            .expect("the qualified frame should retain a surface certificate")
            .iter()
            .any(|tactic| matches!(
                tactic,
                ProofTactic::FrameUsing {
                    region: Some(CodeRegionRef::Loop(0)),
                    premises,
                } if premises.len() == 1
            )),
        "the Proof-owned region frame must retain its explicit premise"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &[("fill_n.c", c_source)],
        "fill_n",
        CProofClaim::Grouped,
    )
    .expect("the premise-bearing qualified frame should expand");
    verify_c0_sources(&expanded, &[("fill_n.c", c_source)])
        .expect("the retained premise-bearing frame should independently reverify");

    let unavailable =
        click_source.replace("n >= 0;\n                }", "n < 0;\n                }");
    let error = verify_c0_sources(&unavailable, &[("fill_n.c", c_source)])
        .expect_err("a qualified frame must check its explicit premise");
    assert!(
        error
            .message()
            .contains("requires an exact available premise"),
        "{}",
        error.message()
    );
}

#[test]
fn frame_label_region_resolves_a_frontier_loop_label() {
    // A `loop as <label>` tactic declares the only labeled code region the
    // surface syntax can express; `frame(<label>)` must resolve it.
    let c_source = r#"
            int32 fill2(int32* p) {
                int32 i;
                i = 0;
                while (i < 2) {
                    p[i] = i;
                    i = i + 1;
                }
                return p[2];
            }
        "#;
    let click_source = r#"
            verifying "fill2.c";

            int32 fill2(int32* p) {
                requires loadable(p[0..3]);
                consumes p[0..3];
                ensures preserved: p[2] == old(p[2]);
            } by {
                step();
                step();
                loop as write_phase {
                    invariant i >= 0;
                    invariant i <= 2;
                    mutable p[0..2] by frame;
                    initialize by simp;
                    preserve by {
                        step();
                        step();
                        close_invariants();
                    }
                }
                step();
                frame(write_phase);
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("fill2.c", c_source)])
        .expect("a frame qualified by a loop label should resolve the frontier loop clause");
}

#[test]
fn frame_loop_region_without_effect_clause_reports_missing_clause() {
    let c_source = r#"
            int32 fill2(int32* p) {
                int32 i;
                i = 0;
                while (i < 2) {
                    p[i] = i;
                    i = i + 1;
                }
                return p[2];
            }
        "#;
    let click_source = r#"
            verifying "fill2.c";

            int32 fill2(int32* p) {
                requires loadable(p[0..3]);
                consumes p[0..3];
                ensures preserved: p[2] == old(p[2]);
            } by {
                step();
                step();
                loop {
                    invariant i >= 0;
                    invariant i <= 2;
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

    let error = verify_c0_sources(click_source, &[("fill2.c", c_source)])
        .expect_err("a qualified frame without a loop effect clause should fail");
    assert!(
        error.message().contains(
            "`frame(loop(0))` needs a loop effect clause such as `mutable` or `immutable`; \
             declare one in this proof's `loop` tactic for loop(0)"
        ),
        "{}",
        error.message()
    );
}
