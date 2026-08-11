use super::*;

#[test]
fn defined_fact_makes_simple_statement_step_explicit() {
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

    verify_c0_sources(click_source, &[("increment.c", c_source)])
        .expect("an explicit definedness theorem should satisfy simple tactic");
}

#[test]
fn apply_using_replays_only_with_its_explicit_premises() {
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
                apply(increment_is_defined(x)) using {
                    x < 2147483647;
                }
                step();
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("increment.c", c_source)])
        .expect("explicit theorem premises should replay");

    let missing_premise = click_source.replace(
        "apply(increment_is_defined(x)) using {
                    x < 2147483647;
                }",
        "apply(increment_is_defined(x)) using {}",
    );
    let error = verify_c0_sources(&missing_premise, &[("increment.c", c_source)])
        .expect_err("apply using must not search ambient facts for an omitted premise");
    assert!(
        error.message().contains("required exact fact"),
        "{}",
        error.message()
    );
}

#[test]
fn apply_using_uses_ambient_loadability_only_to_lower_explicit_premises() {
    let c_source = r#"
            int32 first(int32* data) {
                return data[0];
            }
        "#;
    let click_source = r#"
            verifying "first.c";

            theorem preserve_equal(x: int32, y: int32) {
                requires x == y;
                ensures x == y by {
                    simp();
                }
            }

            int32 first(int32* data) {
                views data[0..1];
                ensures result == data[0];
            } by {
                have data[0] == data[0] by simp;
                step();
                apply(preserve_equal(data[0], data[0])) using {
                    data[0] == data[0];
                }
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("first.c", c_source)]).expect(
        "ambient loadability may lower an explicit premise without becoming a theorem premise",
    );
}

#[test]
fn source_expander_makes_theorem_application_premises_explicit() {
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

    let expanded = expand_c0_claim_source(
        click_source,
        &[("increment.c", c_source)],
        "increment",
        CProofClaim::Grouped,
    )
    .expect("bare theorem application should expand");

    assert!(expanded.contains("apply(increment_is_defined(x)) using {"));
    assert!(expanded.contains("x < 2147483647;"));
    verify_c0_sources(&expanded, &[("increment.c", c_source)])
        .expect("expanded theorem application should replay");
}

#[test]
fn defined_rejects_concrete_undefined_expression() {
    let click_source = r#"
            theorem overflow_is_defined() {
                ensures defined(2147483647 + 1) by {
                    normalize();
                }
            }
        "#;

    let error = verify_c0_sources(click_source, &[])
        .expect_err("a concretely overflowing expression is not defined");
    assert!(
        error.message().contains("goal did not normalize to true"),
        "{}",
        error.message()
    );
}

#[test]
fn failed_point_normalize_does_not_dump_internal_memory() {
    let c_source = r#"
        int32 read(int32* data) {
            return data[0];
        }
    "#;
    let click_source = r#"
        verifying "read.c";

        int32 read(int32* data) {
            requires loadable(data[0..1]);
            views data[0..1];
            ensures result == 1;
        } by {
            step();
            have result == 1 by {
                normalize();
            }
            assumption();
        }
    "#;

    let error = verify_c0_sources(click_source, &[("read.c", c_source)])
        .expect_err("an unknown loaded value must not normalize to one");
    assert!(
        error.message().contains("goal did not normalize to true"),
        "{}",
        error.message()
    );
    assert!(
        !error.message().contains("CMemory {"),
        "{}",
        error.message()
    );
}

#[test]
fn parses_local_have_proof_tactic() {
    let source = FILL3_CLICK.replace(
        "by auto;",
        "by { have n < 2147483647 by simp; execute(); simp(); }",
    );
    let file = parse(&source).expect("local have tactic should parse");
    let tactics = file.function_blocks()[0].ensures()[0]
        .proof()
        .tactics()
        .expect("expected tactics");

    assert!(matches!(
        &tactics[0],
        ProofTactic::Have(ProofHave {
            proof: Proof::Tactic(SmartTactic::Simp),
            ..
        })
    ));
    assert_eq!(
        &tactics[1..],
        &[ProofTactic::SmartExecute, ProofTactic::Simp]
    );
}

#[test]
fn point_proof_intro_places_forall_binder_in_surface_scope() {
    let c_source = r#"
        int32 forall_scope(int32 value) {
            return value;
        }
    "#;
    let click_source = r#"
        verifying "forall_scope.c";

        int32 forall_scope(int32 value) {
            ensures forall (k: int32) {
                (k == k and value == value) implies k == k
            } by {
                execute();
                have forall (k: int32) {
                    (k == k and value == value) implies k == k
                } by {
                    intro();
                    intro();
                    extract(k == k);
                    assumption();
                }
                assumption();
            }
        }
    "#;

    verify_c0_sources(click_source, &[("forall_scope.c", c_source)])
        .expect("the introduced forall binder should be available to later surface tactics");
}

#[test]
fn parses_proof_if_tactic() {
    let source = FILL3_CLICK.replace(
        "by auto;",
        "by { if n <= 0 { execute(); simp(); } else { execute(); simp(); } }",
    );
    let file = parse(&source).expect("proof if should parse");
    let tactics = file.function_blocks()[0].ensures()[0]
        .proof()
        .tactics()
        .expect("expected tactics");

    assert!(matches!(
        &tactics[0],
        ProofTactic::If(ProofIf {
            then_tactics,
            else_tactics,
            ..
        }) if then_tactics == &[ProofTactic::SmartExecute, ProofTactic::Simp]
            && else_tactics == &[ProofTactic::SmartExecute, ProofTactic::Simp]
    ));
}

#[test]
fn parses_existential_proof_tactics() {
    let source = FILL3_CLICK.replace(
        "by auto;",
        "by { execute(); choose(k from requirement has_k); witness(j = k + 1); simp(); }",
    );
    let file = parse(&source).expect("existential explicit proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some(
            [
                ProofTactic::SmartExecute,
                ProofTactic::Choose(ProofChoice {
                    name: "k".to_string(),
                    source: ProofFactSource::RequirementLabel("has_k".to_string()),
                }),
                ProofTactic::Witness(ProofWitness {
                    name: "j".to_string(),
                    value: ContractExpression::Add(
                        Box::new(current_var("k")),
                        Box::new(current_int(1)),
                    ),
                }),
                ProofTactic::Simp,
            ]
            .as_slice()
        )
    );
}

#[test]
fn parses_labeled_requirement() {
    let source = r#"
            verifying "id.c";

            int32 id(int32 x) {
                requires has_x: exists (k: int32) { k == x };
                ensures result == x by auto;
            }
        "#;
    let file = parse(source).expect("labeled requirement should parse");
    let requirement = &file.function_blocks()[0].requires()[0];

    assert_eq!(requirement.label(), Some("has_x"));
    assert!(matches!(
        requirement.inner(),
        Requirement::Proposition(ClickProposition::Exists { .. })
    ));
}

#[test]
fn parses_unnamed_ensure_clause() {
    let source = FILL3_CLICK.replace("ensures returns_second: result == 2", "ensures result == 2");
    let file = parse(&source).expect("sidecar should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(ensure.name(), None);
    assert_eq!(
        ensure.ensure(),
        &ensure_comparison(
            current_var("result"),
            ComparisonOperator::Equal,
            current_int(2),
        )
    );
}

#[test]
fn parses_simp_tactic() {
    let source = FILL3_CLICK.replace("by auto", "by simp");
    let file = parse(&source).expect("sidecar should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert!(matches!(ensure.proof().tactic(), Some(SmartTactic::Simp)));
}

#[test]
fn parses_frame_tactic() {
    let source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires loadable(p[0..2]);
                mutable p[1..2] by frame;
                ensures returns_written: result == 9 by auto;
            }
        "#;
    let file = parse(source).expect("frame tactic should parse");
    let effect = &file.function_blocks()[0].effects()[0];

    assert!(matches!(effect.proof().tactic(), Some(SmartTactic::Frame)));
}

#[test]
fn parses_memory_postcondition() {
    let source = FILL3_CLICK.replace("result == 2", "p[2] == 2");
    let file = parse(&source).expect("sidecar should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.ensure(),
        &ensure_comparison(
            current_index("p", 2),
            ComparisonOperator::Equal,
            current_int(2),
        )
    );
}

#[test]
fn parses_old_memory_postcondition() {
    let source = FILL3_CLICK.replace("result == 2", "p[0] == old(p[0])");
    let file = parse(&source).expect("sidecar should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.ensure(),
        &ensure_comparison(
            current_index("p", 0),
            ComparisonOperator::Equal,
            old_index("p", 0),
        )
    );
}

#[test]
fn rejects_legacy_structural_region_syntax() {
    let source = r#"
            verifying "count.c";

            int32 count() {
                loop 0 {
                    invariant i >= 0;
                }

                ensures result == 3 by auto;
            }
        "#;
    let error = parse(source).expect_err("legacy loop block syntax should fail");

    assert!(
        error.message().contains("expected `let`, `requires`"),
        "{}",
        error.message()
    );
}

#[test]
fn rejects_legacy_proof_tactic_region_syntax() {
    let source = FILL3_CLICK.replace("by auto;", "by { execute(); frame(loop 0); }");
    let error = parse(&source).expect_err("legacy proof tactic region syntax should fail");

    assert!(
        error.message().contains("expected `(`"),
        "{}",
        error.message()
    );
}

#[test]
fn parses_click_proposition_syntax() {
    let source = r#"
            verifying "logic.c";

            predicate nonnegative(x: int32) {
                x >= 0
            }

            int32 logic(int32 x) {
                requires x >= 0 and x < 10;
                requires nonnegative(x);
                ensures bounded: result >= 0 and result < 10 by auto;
                ensures implication: result == x implies result >= 0 by auto;
                ensures named_predicate: nonnegative(result) by auto;
                ensures quantified: forall (k: int32) {
                    0 <= k implies k >= 0
                } by auto;
                immutable by auto;
                mutable p[0..n], q[1..m] by auto;
            }
        "#;
    let file = parse(source).expect("proposition syntax should parse");
    let function = &file.function_blocks()[0];

    assert_eq!(file.predicate_definitions().len(), 1);
    assert_eq!(file.predicate_definitions()[0].name(), "nonnegative");
    assert!(matches!(
        function.requires()[0],
        Requirement::Proposition(ClickProposition::And(_, _))
    ));
    assert!(matches!(
        function.requires()[1],
        Requirement::Proposition(ClickProposition::PredicateCall { .. })
    ));
    assert!(matches!(
        function.ensures()[0].ensure(),
        Ensure::Proposition(ClickProposition::And(_, _))
    ));
    assert!(matches!(
        function.ensures()[1].ensure(),
        Ensure::Proposition(ClickProposition::Implies(_, _))
    ));
    assert!(matches!(
        function.ensures()[2].ensure(),
        Ensure::Proposition(ClickProposition::PredicateCall { .. })
    ));
    assert!(matches!(
        function.ensures()[3].ensure(),
        Ensure::Proposition(ClickProposition::ForAll { .. })
    ));
    assert_eq!(function.effects().len(), 2);
    assert!(matches!(function.effects()[0].effect(), Effect::Immutable));
    match function.effects()[1].effect() {
        Effect::Mutable(segments) => assert_eq!(segments.len(), 2),
        effect => panic!("expected mutable effect, got {effect:?}"),
    }
}

#[test]
fn parses_rust_style_let_annotations() {
    let source = r#"
            function inc_with_let(x: int32) -> int32 {
                let next: int32 = x + 1;
                next
            }
        "#;
    let file = parse(source).expect("Rust-style let annotation should parse");
    let body = file.click_function_definitions()[0].body();

    assert!(matches!(
        body,
        ContractExpression::Let {
            name,
            c_type: Some(C0Type::Int32),
            ..
        } if name == "next"
    ));
}

#[test]
fn parses_contract_level_let_bindings() {
    let source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                let expected: int32 = x;

                ensures result_value: result == expected by auto;
            }
        "#;
    let file = parse(source).expect("contract-level let should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert!(matches!(
        ensure.ensure(),
        Ensure::Proposition(ClickProposition::Comparison {
            right: ContractExpression::Let {
                name,
                c_type: Some(C0Type::Int32),
                ..
            },
            ..
        }) if name == "expected"
    ));
}

#[test]
fn parses_contract_level_let_where_bindings() {
    let source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                let k: int32 where k == x;

                ensures result_value: result == k by auto;
            }
        "#;
    let file = parse(source).expect("contract-level let-where should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert!(matches!(
        ensure.ensure(),
        Ensure::Proposition(ClickProposition::Exists {
            c_type: C0Type::Int32,
            name,
            body,
        }) if name == "k"
            && matches!(body.as_ref(), ClickProposition::And(_, _))
    ));
}

#[test]
fn parses_proposition_let_where_bindings() {
    let source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result_value:
                    let k: int32 where k == x;
                    result == k
                    by auto;
            }
        "#;
    let file = parse(source).expect("proposition let-where should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert!(matches!(
        ensure.ensure(),
        Ensure::Proposition(ClickProposition::Exists {
            c_type: C0Type::Int32,
            name,
            ..
        }) if name == "k"
    ));
}

#[test]
fn rejects_contract_let_parameter_name_conflict() {
    let source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                let x = 0;

                ensures result_value: result == x by auto;
            }
        "#;
    let error = parse(source).expect_err("contract let should not reuse parameter name");

    assert!(
        error
            .message()
            .contains("contract `let` `x` conflicts with a C parameter")
    );
}

#[test]
fn rejects_unknown_predicate_call() {
    let source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures unknown(x) by auto;
            }
        "#;

    let error = parse(source).expect_err("unknown predicate should fail");

    assert!(
        error.message().contains("unknown predicate `unknown`"),
        "{}",
        error.message()
    );
}

#[test]
fn rejects_predicate_call_with_wrong_arity() {
    let source = r#"
            verifying "identity.c";

            predicate nonnegative(x: int32) {
                x >= 0
            }

            int32 identity(int32 x) {
                ensures nonnegative(x, x) by auto;
            }
        "#;

    let error = parse(source).expect_err("wrong predicate arity should fail");

    assert!(
        error
            .message()
            .contains("predicate `nonnegative` expects 1 argument(s), got 2"),
        "{}",
        error.message()
    );
}

#[test]
// An assumed `requires` carries its own definedness: `sorted_pair(p)` cannot be
// true in a state where `p[0]`/`p[1]` do not denote, so assuming the
// requirement also assumes their loadability. The dual direction stays a proof
// obligation — see the two tests below.
fn verifies_opaque_predicate_from_requirement() {
    let c_source = r#"
            int32 identity_pointer_fact(int32* p) {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "identity_pointer_fact.c";

            predicate sorted_pair(p: int32*) {
                p[0] <= p[1]
            }

            int32 identity_pointer_fact(int32* p) {
                requires sorted_pair(p);
                ensures still_sorted: sorted_pair(p) by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("identity_pointer_fact.c", c_source)])
        .expect("exact opaque predicate fact should verify");

    assert_eq!(verified.len(), 1);
}

/// The definedness of an *assumed* requirement rides along with it, but the
/// dual direction must not: proving a heap-dependent `ensures` still owes the
/// loadability its loads need, or a proof could help itself to the readability
/// of the very memory it is making a claim about.
#[test]
fn heap_dependent_ensures_still_owes_its_loads() {
    let c_source = r#"
            int32 claim_sorted(int32* p) {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "claim_sorted.c";

            predicate sorted_pair(p: int32*) {
                p[0] <= p[1]
            }

            int32 claim_sorted(int32* p) {
                ensures sorted_pair(p) by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("claim_sorted.c", c_source)])
        .expect_err("an ensures with no requires must not assume its own definedness");
    assert!(
        error.message().contains("unproved") || error.message().contains("claim_sorted.ensures_0"),
        "{}",
        error.message()
    );
}

/// A caller must establish the callee's heap-dependent precondition, including
/// the loadability its evaluation needs. This is the obligation side of the
/// definedness rule; if it ever starts passing, the assumption side has become
/// a way to manufacture readability out of nothing.
#[test]
fn call_site_owes_the_definedness_of_a_heap_dependent_precondition() {
    let callee_source = r#"
            int32 needs_sorted(int32* p) {
                return 0;
            }
        "#;
    let caller_source = r#"
            int32 calls_it(int32* q) {
                int32 r;
                r = needs_sorted(q);
                return r;
            }
        "#;
    let click_source = r#"
            verifying "needs_sorted.c";
            verifying "calls_it.c";

            predicate sorted_pair(p: int32*) {
                p[0] <= p[1]
            }

            int32 needs_sorted(int32* p) {
                requires sorted_pair(p);
                ensures result == 0;
            } by auto;

            int32 calls_it(int32* q) {
                ensures result == 0;
            } by auto;
        "#;

    verify_c0_sources(
        click_source,
        &[
            ("needs_sorted.c", callee_source),
            ("calls_it.c", caller_source),
        ],
    )
    .expect_err("the call site must establish the precondition it relies on");
}

#[test]
fn unfolds_predicate_requirement_to_prove_consequence() {
    let c_source = r#"
            int32 keep_pair(int32* p) {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "keep_pair.c";

            predicate sorted_pair(p: int32*) {
                p[0] <= p[1]
            }

            int32 keep_pair(int32* p) {
                requires loadable(p[0..2]);
                requires sorted_pair(p);
                ensures consequence: p[0] <= p[1] by {
                    execute();
                    unfold(sorted_pair);
                    simp();
                }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("keep_pair.c", c_source)])
        .expect("unfolded predicate requirement should prove its body");

    assert_eq!(verified.len(), 1);
    assert_eq!(
        verified[0].proof_tactics(),
        Some(
            [
                ProofTactic::SmartExecute,
                ProofTactic::UnfoldPredicate("sorted_pair".to_string()),
                ProofTactic::Simp,
            ]
            .as_slice()
        )
    );
}

#[test]
fn unfolds_predicate_goal_to_prove_compare_swap_sorted() {
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
                ensures sorted: sorted_pair(p) by {
                    execute();
                    unfold(sorted_pair);
                    simp();
                }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("compare_swap2.c", c_source)])
        .expect("unfolded predicate goal should prove compare-swap sortedness");

    assert_eq!(verified.len(), 2);
}

#[test]
fn unfolds_general_sorted_predicate() {
    let c_source = r#"
            int32 keep_sorted(int32* p, int32 n) {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "keep_sorted.c";

            predicate sorted(p: int32*, n: int32) {
                forall (i: int32) {
                    forall (j: int32) {
                        0 <= i and 0 <= j and i < j and j < n implies p[i] <= p[j]
                    }
                }
            }

            int32 keep_sorted(int32* p, int32 n) {
                requires n >= 0;
                requires loadable(p[0..n]);
                requires sorted(p, n);
                ensures still_sorted: sorted(p, n) by {
                    execute();
                    unfold(sorted);
                    simp();
                }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("keep_sorted.c", c_source)])
        .expect("general sorted predicate should unfold deterministically");

    assert_eq!(verified.len(), 1);
}

#[test]
fn verifies_click_proposition_logic() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures prop_logic: result == x and not (result != x) by auto;
                ensures prop_implies: result == x implies result == x by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)])
        .expect("proposition logic should verify");

    assert_eq!(verified.len(), 2);
}

#[test]
fn verifies_simp_normalizes_simple_postconditions() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures add_zero: result == x + 0 by { execute(); simp(); }
                ensures prop_simp: result == x and not (result != x) by { execute(); simp(); }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)])
        .expect("simp should prove local normalized postconditions");

    assert_eq!(verified.len(), 2);
    assert_eq!(verified[0].proof_kind(), ProofKind::TacticScript);
    assert_eq!(verified[1].proof_kind(), ProofKind::TacticScript);
}

#[test]
fn proof_sugar_and_bare_smart_tactics_have_the_same_frontier_semantics() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let simp_errors = ["by simp;", "by { simp; }", "by simp;"].map(|proof| {
        let source = format!(
            "verifying \"identity.c\"; int32 identity(int32 x) {{ ensures result == x {proof} }}"
        );
        verify_c0_sources(&source, &[("identity.c", c_source)])
            .expect_err("simp at function entry should not execute")
            .message()
            .to_string()
    });
    assert_eq!(simp_errors[0], simp_errors[1]);
    assert_eq!(simp_errors[0], simp_errors[2]);
    assert!(simp_errors[0].contains("requires execution to reach function exit first"));

    let frame_errors = ["by frame;", "by { frame(); }"].map(|proof| {
        let source =
            format!("verifying \"identity.c\"; int32 identity(int32 x) {{ immutable {proof} }}");
        verify_c0_sources(&source, &[("identity.c", c_source)])
            .expect_err("frame at function entry should not execute")
            .message()
            .to_string()
    });
    assert_eq!(frame_errors[0], frame_errors[1]);
    assert!(frame_errors[0].contains("requires execution to reach function exit first"));
}

#[test]
fn instantiate_specializes_a_universal_fact_at_an_explicit_value() {
    let c_source = r#"
        int32 pick(int32 value) {
            return value;
        }
    "#;
    let click_source = r#"
        verifying "pick.c";

        int32 pick(int32 value) {
            requires bounded: forall (k: int32) {
                0 <= k and k < 3 implies k <= value
            };
            ensures two_le: 2 <= value;
        } by {
            execute();
            have 2 <= value by {
                instantiate(forall (k: int32) {
                    0 <= k and k < 3 implies k <= value
                }, 2) using {}
                assumption();
            }
            assumption();
        }
    "#;

    verify_c0_sources(click_source, &[("pick.c", c_source)])
        .expect("instantiating the universal requirement at 2 should prove the bound");
}

#[test]
fn instantiate_does_not_discharge_guards_from_ambient_facts() {
    let c_source = r#"
        int32 pick(int32 value, int32 n) {
            return value;
        }
    "#;
    let click_source = r#"
        verifying "pick.c";

        int32 pick(int32 value, int32 n) {
            requires wide: n >= 3;
            requires bounded: forall (k: int32) {
                0 <= k and k < n implies k <= value
            };
            ensures two_le: 2 <= value;
        } by {
            execute();
            have 2 <= value by {
                instantiate(forall (k: int32) {
                    0 <= k and k < n implies k <= value
                }, 2) using {}
                assumption();
            }
            assumption();
        }
    "#;

    let error = verify_c0_sources(click_source, &[("pick.c", c_source)])
        .expect_err("the symbolic upper-bound guard must name its evidence");
    assert!(
        error
            .message()
            .contains("does not follow from the listed evidence"),
        "unexpected error: {}",
        error.message()
    );
}
