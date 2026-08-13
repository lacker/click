use super::*;

#[test]
fn parses_logical_if_with_execution_tactics() {
    let source = FILL3_CLICK.replace(
        "by auto;",
        "by { if n <= 0 { step(); execute(); simp(); } else { step(); execute(); simp(); } }",
    );
    let file = parse(&source).expect("explicit branch execution tactics should parse");
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
        }) if then_tactics.first() == Some(&ProofTactic::SmartStep)
            && else_tactics.first() == Some(&ProofTactic::SmartStep)
    ));
}

#[test]
fn parses_frontier_branch_tactic() {
    let source = FILL3_CLICK.replace(
        "by auto;",
        "by { branch { then { step(); } else { execute(); } } }",
    );
    let file = parse(&source).expect("frontier branch tactic should parse");
    let tactics = file.function_blocks()[0].ensures()[0]
        .proof()
        .tactics()
        .expect("expected tactics");

    assert!(matches!(
        &tactics[0],
        ProofTactic::Branch(ProofBranch {
            ensuring: None,
            then_tactics,
            else_tactics,
        }) if then_tactics == &[ProofTactic::SmartStep]
            && else_tactics == &[ProofTactic::SmartExecute]
    ));
}

#[test]
fn parses_frontier_branch_ensuring_interface() {
    let source = FILL3_CLICK.replace(
        "by auto;",
        "by { branch { ensuring { fact i >= 0; owns p[0..3]; } then { step(); } else { execute(); } } }",
    );
    let file = parse(&source).expect("frontier branch ensuring interface should parse");
    let tactics = file.function_blocks()[0].ensures()[0]
        .proof()
        .tactics()
        .expect("expected tactics");

    assert!(matches!(
        &tactics[0],
        ProofTactic::Branch(ProofBranch {
            ensuring: Some(assertions),
            then_tactics,
            else_tactics,
        }) if matches!(assertions.as_slice(), [
            ProofAssertion::Fact(_),
            ProofAssertion::Resource(ResourceClause::Write(_)),
        ]) && then_tactics == &[ProofTactic::SmartStep]
            && else_tactics == &[ProofTactic::SmartExecute]
    ));
}

#[test]
fn rejects_removed_reach_tactic() {
    let source = FILL3_CLICK.replace(
        "by auto;",
        "by { reach(statement(1).exit) ensuring { fact i >= 0; } by { step(); } }",
    );
    let error = parse(&source).expect_err("removed reach tactic should not parse");

    assert!(error.message().contains("unknown tactic `reach`"));
}

#[test]
fn empty_proof_if_branches_contribute_only_their_case_split() {
    // Owner decision 2026-07-31: an empty `if` branch is legal in a proof
    // script — it contributes its case split and every path goal stays owed
    // at path end. Pure case-split certificates expand to exactly this shape.
    let c_source = r#"
            int32 sign_bit(int32 x) {
                if (x < 0) {
                    return 1;
                }
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "sign.c";

            int32 sign_bit(int32 x) {
                ensures result == 0 or result == 1;
            } by {
                execute();
                if x < 0 {
                } else {
                }
                simp();
            }
        "#;
    verify_c0_sources(click_source, &[("sign.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "empty proof-if branches should parse and verify: {}",
            error.message()
        )
    });
}

#[test]
fn parses_execute_until_proof_tactic() {
    let source = FILL3_CLICK.replace(
        "by auto;",
        "by { execute_until(statement(1)); execute(); simp(); }",
    );
    let file = parse(&source).expect("execute_until explicit proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some(
            [
                ProofTactic::ExecuteUntil(CodeRegionRef::Statement(1)),
                ProofTactic::SmartExecute,
                ProofTactic::Simp,
            ]
            .as_slice()
        )
    );
}

#[test]
fn parses_unfold_proof_tactic() {
    let source = FILL3_CLICK.replace("by auto;", "by { execute(); unfold(sorted); simp(); }");
    let file = parse(&source).expect("unfold explicit proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some(
            [
                ProofTactic::SmartExecute,
                ProofTactic::UnfoldPredicate("sorted".to_string()),
                ProofTactic::Simp,
            ]
            .as_slice()
        )
    );
}

#[test]
fn parses_apply_theorem_proof_tactic() {
    let source = FILL3_CLICK.replace(
        "by auto;",
        "by { execute(); apply(nonnegative(result)); simp(); }",
    );
    let file = parse(&source).expect("apply explicit proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some(
            [
                ProofTactic::SmartExecute,
                ProofTactic::ApplyTheorem(TheoremApplication {
                    name: "nonnegative".to_string(),
                    arguments: vec![current_var("result")],
                }),
                ProofTactic::Simp,
            ]
            .as_slice()
        )
    );
}

#[test]
fn parses_apply_theorem_with_explicit_premises() {
    let source = FILL3_CLICK.replace(
        "by auto;",
        "by {
            execute();
            apply(nonnegative(result)) using {
                result >= 0;
            }
            simp();
        }",
    );
    let file = parse(&source).expect("explicit-premise theorem application should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert!(matches!(
        &ensure.proof().tactics().expect("expected tactics")[1],
        ProofTactic::ApplyTheoremUsing { premises, .. } if premises.len() == 1
    ));
}

#[test]
fn parses_transport_with_explicit_premises() {
    let source = FILL3_CLICK.replace(
        "by auto;",
        "by {
            step();
            transport(old(p[0]) == 0, p[0] == 0) using {
                old(p[0]) == 0;
            }
            execute();
            simp();
        }",
    );
    let file = parse(&source).expect("explicit-premise transport should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert!(matches!(
        &ensure.proof().tactics().expect("expected tactics")[1],
        ProofTactic::TransportUsing { premises, .. } if premises.len() == 1
    ));
}

#[test]
fn parses_and_classifies_simple_and_smart_tactics() {
    let source = r#"
            theorem rewritten(x: int32, y: int32) {
                requires x == y;
                ensures x == y by {
                    rewrite(x == y);
                    normalize();
                }
            }
        "#;
    let file = parse(source).expect("simple tactics should parse");
    let tactics = file.theorem_definitions()[0].ensures()[0]
        .proof()
        .tactics()
        .expect("expected tactics");

    assert!(matches!(
        tactics[0].class(),
        TacticClass::Simple(SimpleTactic::Rewrite)
    ));
    assert!(matches!(
        tactics[1].class(),
        TacticClass::Simple(SimpleTactic::Normalize)
    ));
    assert!(matches!(
        ProofTactic::Simp.class(),
        TacticClass::Smart(SmartTacticKind::Simp)
    ));
    assert!(matches!(
        ProofTactic::SimpUsing(ProofSimpUsing {
            premises: Vec::new(),
        })
        .class(),
        TacticClass::Smart(SmartTacticKind::Simp)
    ));
    assert!(matches!(
        ProofTactic::SmartStep.class(),
        TacticClass::Smart(SmartTacticKind::SmartStep)
    ));
    let application = TheoremApplication {
        name: "rewritten".to_string(),
        arguments: vec![current_int(0), current_int(0)],
    };
    assert!(matches!(
        ProofTactic::ApplyTheorem(application.clone()).class(),
        TacticClass::Smart(SmartTacticKind::ApplyTheorem)
    ));
    assert!(matches!(
        ProofTactic::ApplyTheoremUsing {
            application,
            premises: vec![ClickProposition::Defined {
                expression: current_int(0),
            }],
        }
        .class(),
        TacticClass::Simple(SimpleTactic::ApplyTheorem)
    ));
    let transport_source = ClickProposition::Defined {
        expression: current_int(0),
    };
    let transport_target = ClickProposition::Defined {
        expression: current_int(1),
    };
    assert!(matches!(
        ProofTactic::Transport {
            source: transport_source.clone(),
            target: transport_target.clone(),
        }
        .class(),
        TacticClass::Smart(SmartTacticKind::FactTransport)
    ));
    assert!(matches!(
        ProofTactic::TransportUsing {
            source: transport_source,
            target: transport_target,
            premises: Vec::new(),
        }
        .class(),
        TacticClass::Simple(SimpleTactic::FactTransport)
    ));
    assert!(matches!(
        ProofTactic::StepUsing(Vec::new()).class(),
        TacticClass::Simple(SimpleTactic::StatementTransition)
    ));
    assert!(matches!(
        ProofTactic::StepUsing(vec![ClickProposition::Defined {
            expression: current_int(0),
        }])
        .class(),
        TacticClass::Simple(SimpleTactic::StatementTransition)
    ));
    assert!(matches!(
        ProofTactic::FoldResource(ResourceClause::Declared {
            access: ResourceAccessMode::Own,
            kind: ResourceKind::Composite,
            name: "cell".to_string(),
            arguments: vec![],
            parameter_types: vec![],
        })
        .class(),
        TacticClass::Simple(SimpleTactic::FoldResource)
    ));
    assert!(matches!(
        ProofTactic::FrameUsing {
            region: None,
            premises: Vec::new(),
        }
        .class(),
        TacticClass::Simple(SimpleTactic::Frame)
    ));
    assert!(matches!(
        ProofTactic::FrameUsing {
            region: None,
            premises: Vec::new(),
        }
        .class(),
        TacticClass::Simple(SimpleTactic::Frame)
    ));
    assert!(matches!(
        ProofTactic::CloseInvariants.class(),
        TacticClass::Simple(SimpleTactic::CloseInvariants)
    ));
    assert!(matches!(
        ProofTactic::Mark("before_write".to_string()).class(),
        TacticClass::Simple(SimpleTactic::Mark)
    ));
    assert!(matches!(
        ProofTactic::SmartFrame(None).class(),
        TacticClass::Smart(SmartTacticKind::Frame)
    ));
    assert!(matches!(
        ProofTactic::SmartStep.class(),
        TacticClass::Smart(SmartTacticKind::SmartStep)
    ));
    assert!(matches!(
        ProofTactic::SmartStep.class(),
        TacticClass::Smart(SmartTacticKind::SmartStep)
    ));
    assert!(matches!(
        ProofTactic::SmartExecute.class(),
        TacticClass::Smart(SmartTacticKind::SmartExecute)
    ));
    assert!(matches!(
        ProofTactic::ExecuteUntil(CodeRegionRef::Statement(1)).class(),
        TacticClass::Smart(SmartTacticKind::ExecuteUntil)
    ));
}

#[test]
fn canonical_tactic_printer_round_trips_nested_surface_certificate() {
    let nonnegative = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
        operator: ComparisonOperator::GreaterEqual,
        right: ContractExpression::CFragment(CExpression::Value(int32(0))),
    };
    let tactics = vec![
        ProofTactic::Mark("before_step".to_string()),
        ProofTactic::StepUsing(vec![nonnegative.clone()]),
        ProofTactic::If(ProofIf {
            condition: nonnegative.clone(),
            then_tactics: vec![ProofTactic::Have(ProofHave {
                proposition: nonnegative.clone(),
                proof: Proof::Script(vec![ProofTactic::Assumption]),
            })],
            else_tactics: vec![ProofTactic::Normalize],
        }),
        ProofTactic::CloseInvariants,
    ];
    let certificate = SimpleProof::from_proof_tactics(&tactics)
        .expect("test tactics should form a surface certificate");
    let printed = format_simple_proof(&certificate);
    let source = format!(
        r#"
            verifying "printer.c";

            int32 printer(int32 x) {{
                ensures x == x;
            }} {printed}
        "#
    );
    let parsed = parse(&source).expect("printed certificate should parse");
    assert_eq!(
        parsed.function_blocks()[0].grouped_proof(),
        Some(&Proof::Script(tactics))
    );
}

#[test]
fn canonical_tactic_printer_round_trips_cases_certificate() {
    let nonnegative = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
        operator: ComparisonOperator::GreaterEqual,
        right: ContractExpression::CFragment(CExpression::Value(int32(0))),
    };
    let negative = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
        operator: ComparisonOperator::LessThan,
        right: ContractExpression::CFragment(CExpression::Value(int32(0))),
    };
    let disjunction =
        ClickProposition::Or(Box::new(nonnegative.clone()), Box::new(negative.clone()));
    let tactics = vec![
        ProofTactic::Have(ProofHave {
            proposition: disjunction.clone(),
            proof: Proof::Script(vec![ProofTactic::Cases(ProofCases {
                disjunction,
                left_tactics: vec![ProofTactic::Left],
                right_tactics: vec![ProofTactic::Right],
            })]),
        }),
        ProofTactic::Enumerate,
    ];
    let certificate = SimpleProof::from_proof_tactics(&tactics)
        .expect("a cases script should form a surface certificate");
    let printed = format_simple_proof(&certificate);
    let source = format!(
        r#"
            verifying "printer.c";

            int32 printer(int32 x) {{
                ensures x == x;
            }} {printed}
        "#
    );
    let parsed = parse(&source).expect("printed cases certificate should parse");
    assert_eq!(
        parsed.function_blocks()[0].grouped_proof(),
        Some(&Proof::Script(tactics))
    );
}

#[test]
fn simple_proof_round_trips_nested_surface_steps() {
    let reflexive = ClickProposition::Comparison {
        left: current_var("x"),
        operator: ComparisonOperator::Equal,
        right: current_var("x"),
    };
    let tactics = vec![
        ProofTactic::Mark("entry".to_string()),
        ProofTactic::Have(ProofHave {
            proposition: reflexive.clone(),
            proof: Proof::Script(vec![ProofTactic::Normalize]),
        }),
        ProofTactic::Branch(ProofBranch {
            ensuring: Some(vec![ProofAssertion::Fact(reflexive)]),
            then_tactics: vec![ProofTactic::Assumption],
            else_tactics: vec![ProofTactic::Normalize],
        }),
    ];

    let proof = SimpleProof::from_proof_tactics(&tactics)
        .expect("surface tactics should construct a simple proof");

    assert_eq!(proof.to_proof_tactics(), tactics);
    assert!(matches!(
        proof.steps(),
        [
            SimpleProofStep::Mark(_),
            SimpleProofStep::Have { .. },
            SimpleProofStep::Branch { .. }
        ]
    ));
}

#[test]
fn simple_proof_has_no_smart_step_variant() {
    let smart = SimpleProof::from_proof_tactics(&[ProofTactic::Simp])
        .expect_err("smart tactics are not simple proof steps");
    assert_eq!(
        smart.tactic_class(),
        TacticClass::Smart(SmartTacticKind::Simp)
    );
}

#[test]
fn tactic_certificate_accepts_only_simple_tactics() {
    let tactics = vec![
        ProofTactic::Rewrite(ClickProposition::Comparison {
            left: current_var("x"),
            operator: ComparisonOperator::Equal,
            right: current_var("y"),
        }),
        ProofTactic::Normalize,
    ];

    let certificate =
        SimpleProof::from_proof_tactics(&tactics).expect("simple tactics form a certificate");

    assert_eq!(certificate.to_proof_tactics(), tactics);
}

#[test]
fn tactic_certificate_rejects_a_direct_smart_tactic() {
    let error = SimpleProof::from_proof_tactics(&[ProofTactic::Simp])
        .expect_err("a smart tactic cannot be a certificate leaf");

    assert_eq!(
        error.tactic_class(),
        TacticClass::Smart(SmartTacticKind::Simp)
    );
    assert_eq!(error.path(), &[CertificatePathSegment::Tactic(0)]);
}

#[test]
fn tactic_certificate_rejects_smart_tactics_in_nested_control_flow() {
    let condition = ClickProposition::Comparison {
        left: current_var("x"),
        operator: ComparisonOperator::Equal,
        right: current_var("x"),
    };
    let tactics = [ProofTactic::Branch(ProofBranch {
        ensuring: None,
        then_tactics: vec![ProofTactic::If(ProofIf {
            condition,
            then_tactics: vec![ProofTactic::Have(ProofHave {
                proposition: ClickProposition::Comparison {
                    left: current_var("x"),
                    operator: ComparisonOperator::Equal,
                    right: current_var("x"),
                },
                proof: Proof::Script(vec![ProofTactic::Simp]),
            })],
            else_tactics: vec![ProofTactic::Normalize],
        })],
        else_tactics: vec![ProofTactic::Normalize],
    })];

    let error = SimpleProof::from_proof_tactics(&tactics)
        .expect_err("nested smart tactics cannot be hidden in a certificate");

    assert_eq!(
        error.tactic_class(),
        TacticClass::Smart(SmartTacticKind::Simp)
    );
    assert_eq!(
        error.path(),
        &[
            CertificatePathSegment::Tactic(0),
            CertificatePathSegment::ThenBranch,
            CertificatePathSegment::Tactic(0),
            CertificatePathSegment::ThenBranch,
            CertificatePathSegment::Tactic(0),
            CertificatePathSegment::HaveBody,
            CertificatePathSegment::Tactic(0),
        ]
    );
}

#[test]
fn tactic_certificate_treats_an_omitted_nested_proof_as_auto() {
    let tactics = [ProofTactic::Have(ProofHave {
        proposition: ClickProposition::Comparison {
            left: current_var("x"),
            operator: ComparisonOperator::Equal,
            right: current_var("x"),
        },
        proof: Proof::Default,
    })];

    let error = SimpleProof::from_proof_tactics(&tactics)
        .expect_err("an omitted nested proof is smart auto");

    assert_eq!(
        error.tactic_class(),
        TacticClass::Smart(SmartTacticKind::Auto)
    );
    assert_eq!(
        error.path(),
        &[
            CertificatePathSegment::Tactic(0),
            CertificatePathSegment::HaveBody,
        ]
    );
}

const ORDERED_PAIR_C: &str = r#"
    struct pair {
        int32 low;
        int32 high;
    };

    void set_pair(struct pair* pair, int32 bound) {
        pair->low = 0;
        pair->high = bound;
    }
"#;

const ORDERED_PAIR_CLICK: &str = r#"
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

#[test]
fn smart_have_splits_an_unfolded_predicate_conjunction_goal() {
    // The `have`'s smart `simp` closes a predicate body that unfolds to a
    // conjunction of scalar bounds. The constructed certificate must split
    // the conjunction into per-conjunct `have` certificates; before the
    // split, the whole-conjunction goal had no explicit simple certificate.
    verify_c0_sources(ORDERED_PAIR_CLICK, &[("set_pair.c", ORDERED_PAIR_C)]).unwrap_or_else(
        |error| {
            panic!(
                "the unfolded conjunction goal should split per conjunct: {}",
                error.message()
            )
        },
    );
}

#[test]
fn point_have_certifies_a_post_call_fact_across_a_later_store() {
    // After the call to `reset`, the fact `pair->low == 0` is recorded
    // against the call's post-state snapshot; the later store to
    // `pair->high` moves the current memory past it. The mid-proof `have`
    // must still produce a replaying certificate for the fact in its
    // current spelling. (The full stale-spelling rewrite rejection is
    // exercised by `examples/bounded-pool`'s `pool_pipeline`.)
    let reset_source = r#"
        struct pair {
            int32 low;
            int32 high;
        };

        void reset(struct pair* pair) {
            pair->low = 0;
        }
    "#;
    let touch_source = r#"
        struct pair {
            int32 low;
            int32 high;
        };

        void touch(struct pair* pair) {
            reset(pair);
            pair->high = 5;
        }
    "#;
    let click_source = r#"
        verifying "reset.c";
        verifying "touch.c";

        void reset(struct pair* pair) {
            owns object(pair);
            mutable pair->low;

            ensures pair->low == 0;
        } by {
            execute();
            frame();
            simp();
        }

        void touch(struct pair* pair) {
            owns object(pair);
            mutable pair->low, pair->high;

            ensures pair->low == 0;
        } by {
            step();
            step();
            have pair->low == 0 by simp;
            step();
            frame();
            simp();
        }
    "#;

    verify_c0_sources(
        click_source,
        &[("reset.c", reset_source), ("touch.c", touch_source)],
    )
    .unwrap_or_else(|error| {
        panic!(
            "the post-call have should certify without a stale-spelling rewrite: {}",
            error.message()
        )
    });
}

#[test]
fn grouped_outcome_simp_splits_an_unfold_active_conjunction_ensure() {
    // The final `simp` certifies `ordered_pair(pair)` while `unfold` is
    // active, so the kernel goal is already the body conjunction while the
    // surface goal is the predicate call. The certificate must unfold the
    // surface goal in step and split the conjunction.
    let c_source = r#"
        struct pair {
            int32 low;
            int32 high;
        };

        void bump(struct pair* pair) {
            pair->low = pair->low + 1;
        }
    "#;
    let click_source = r#"
        predicate ordered_pair(pair: struct pair*) {
            0 <= pair->low and pair->low <= pair->high
        }

        verifying "bump.c";

        void bump(struct pair* pair) {
            requires ordered_pair(pair);
            requires pair->low < pair->high;
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

    verify_c0_sources(click_source, &[("bump.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "the unfold-active conjunction ensure should split per conjunct: {}",
            error.message()
        )
    });
}
