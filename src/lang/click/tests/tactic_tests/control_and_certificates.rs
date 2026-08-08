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
        ProofTactic::CertifiedStatementStep {
            prerequisite_derivations: Vec::new(),
            exact_premises: Vec::new(),
        }
        .class(),
        TacticClass::Simple(SimpleTactic::CertifiedStatementTransition)
    ));
    assert!(matches!(
        ProofTactic::CertifiedLoopSummaryStep {
            prerequisite_derivations: Vec::new(),
            exact_premises: Vec::new(),
        }
        .class(),
        TacticClass::Simple(SimpleTactic::CertifiedLoopSummaryTransition)
    ));
    assert!(matches!(
        ProofTactic::CertifiedAlternatives(Vec::new()).class(),
        TacticClass::ControlFlow(ControlFlowTactic::CertifiedAlternatives)
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
        ProofTactic::CertifiedFrame(Vec::new()).class(),
        TacticClass::Simple(SimpleTactic::CertifiedFrame)
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
                proof: Proof::Script(vec![ProofTactic::Derive(ProofDerive {
                    premises: vec![nonnegative.clone()],
                })]),
            })],
            else_tactics: vec![ProofTactic::Normalize],
        }),
        ProofTactic::CloseInvariants,
    ];
    let certificate = TacticCertificate::from_proof_tactics(&tactics)
        .expect("test tactics should form a surface certificate");
    let printed = format_tactic_certificate(&certificate);
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
        TacticCertificate::from_proof_tactics(&tactics).expect("simple tactics form a certificate");

    assert_eq!(certificate.tactics(), tactics);
}

#[test]
fn tactic_certificate_rejects_a_direct_smart_tactic() {
    let error = TacticCertificate::from_proof_tactics(&[ProofTactic::Simp])
        .expect_err("a smart tactic cannot be a certificate leaf");

    assert_eq!(
        error.tactic_class(),
        TacticClass::Smart(SmartTacticKind::Simp)
    );
    assert_eq!(error.path(), &[CertificatePathSegment::Tactic(0)]);
}

#[test]
fn tactic_certificate_rejects_internal_replay_evidence() {
    let error = TacticCertificate::from_proof_tactics(&[ProofTactic::CertifiedStatementStep {
        prerequisite_derivations: Vec::new(),
        exact_premises: Vec::new(),
    }])
    .expect_err("internal replay evidence is not a surface tactic");

    assert_eq!(
        error.tactic_class(),
        TacticClass::Simple(SimpleTactic::CertifiedStatementTransition)
    );
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

    let error = TacticCertificate::from_proof_tactics(&tactics)
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

    let error = TacticCertificate::from_proof_tactics(&tactics)
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
