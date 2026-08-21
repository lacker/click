use super::*;

#[test]
fn omitted_ensure_proof_uses_default_prover() {
    let source = FILL3_CLICK.replace(" by auto", "");
    let file = parse(&source).expect("sidecar should parse omitted proof clause");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert!(ensure.proof().is_auto_tactic());
}

#[test]
fn omitted_effect_proof_uses_default_prover() {
    let source = r#"
            verifying "zero.c";

            int32 zero() {
                immutable;
                ensures returns_zero: result == 0;
            }
        "#;
    let file = parse(source).expect("effect proof may be omitted");
    let function = &file.function_blocks()[0];

    assert!(function.effects()[0].proof().is_auto_tactic());
    assert!(function.ensures()[0].proof().is_auto_tactic());
}

#[test]
fn parses_grouped_function_proof() {
    let source = r#"
            verifying "set.c";

            int32 set(int32 p[], int32 value) {
                consumes p[0..1];
                mutable p[0..1];
                produces p[0..1];
                ensures result == value;
                ensures p[0] == value;
            } by {
                execute();
                frame();
                simp();
            }
        "#;
    let file = parse(source).expect("grouped function proof should parse");
    let function = &file.function_blocks()[0];

    assert_eq!(
        function.grouped_proof().and_then(SourceProof::tactics),
        Some(
            [
                ProofTactic::SmartExecute,
                ProofTactic::SmartFrame(None),
                ProofTactic::Simp
            ]
            .as_slice()
        )
    );
    assert!(matches!(
        function.effects()[0].proof(),
        SourceProof::Default
    ));
    assert!(matches!(
        function.ensures()[0].proof(),
        SourceProof::Default
    ));
}

#[test]
fn rejects_mixed_grouped_and_individual_claim_proofs() {
    let source = r#"
            verifying "identity.c";

            int32 identity(int32 value) {
                ensures result == value by auto;
            } by {
                execute();
                simp();
            }
        "#;
    let error = parse(source).expect_err("proof styles must not be mixed");

    assert!(
        error
            .message()
            .contains("a grouped function proof cannot be combined with individual claim proofs")
    );
}

#[test]
fn grouped_function_proof_checks_every_claim() {
    let c_source = r#"
            int32 identity(int32 value) {
                return value;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 value) {
                ensures result == value;
                ensures result != value;
            } by {
                execute();
                simp();
            }
        "#;
    let error = verify_c0_sources(click_source, &[("identity.c", c_source)])
        .expect_err("every grouped postcondition must be checked");

    assert!(
        error.message().contains("identity.ensures_1"),
        "unexpected error: {}",
        error.message()
    );
    assert!(
        error.message().contains("unclosed goal: result != value"),
        "unexpected error: {}",
        error.message()
    );
}

#[test]
fn grouped_function_certificates_share_finalized_specification() {
    let c_source = r#"
            int32 set(int32 p[], int32 value) {
                p[0] = value;
                return value;
            }
        "#;
    let click_source = r#"
            verifying "set.c";

            int32 set(int32 p[], int32 value) {
                consumes p[0..1];
                mutable p[0..1];
                produces p[0..1];
                ensures result == value;
                ensures p[0] == value;
            } by {
                execute();
                frame();
                simp();
            }
        "#;
    let verified = verify_c0_sources(click_source, &[("set.c", c_source)])
        .expect("grouped function should verify");
    let specifications = verified
        .iter()
        .filter(|theorem| theorem.function_block.signature().name() == "set")
        .map(|theorem| &theorem.specification)
        .collect::<Vec<_>>();

    assert_eq!(specifications.len(), 4);
    assert!(specifications.windows(2).all(|pair| pair[0] == pair[1]));
}

#[test]
fn grouped_auto_uses_one_deterministic_execution_proof() {
    let c_source = r#"
            int32 set(int32 p[], int32 value) {
                p[0] = value;
                return value;
            }
        "#;
    let click_source = r#"
            verifying "set.c";

            int32 set(int32 p[], int32 value) {
                consumes p[0..1];
                mutable p[0..1];
                produces p[0..1];
                ensures result == value;
                ensures p[0] == value;
            } by auto;
        "#;
    let _ = crate::kernel::take_checked_function_body_execution_count();
    let verified = verify_c0_sources(click_source, &[("set.c", c_source)])
        .expect("grouped auto proof should verify");
    let expected_tactics = [
        ProofTactic::SmartExecute,
        ProofTactic::FrameUsing {
            region: None,
            premises: Vec::new(),
        },
        ProofTactic::Simp,
    ];

    assert_eq!(verified.len(), 4);
    assert!(
        verified
            .iter()
            .all(|theorem| theorem.proof_tactics() == Some(expected_tactics.as_slice()))
    );
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        1,
        "claim certification and final contract certification should share one checked body execution"
    );
}

#[test]
fn grouped_resource_predicate_proof_reuses_checked_body_execution() {
    let c_source = r#"
            int32 return_zero(int32 p[]) {
                return 0;
            }
        "#;
    let click_source = r#"
            predicate zero_at(p: int32[]) {
                p[0] == 0
            }

            resource zero_cell(p: int32*) {
                owns p[0..1];
                fact zero_at(p);
            }

            verifying "return_zero.c";

            int32 return_zero(int32 p[]) {
                owns zero_cell(p);
                immutable;
                ensures result == 0;
            } by {
                execute();
                frame();
                simp();
            }
        "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    let verified = verify_c0_sources(click_source, &[("return_zero.c", c_source)])
        .expect("resource predicate proof should verify");

    assert_eq!(verified.len(), 3);
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        1,
        "named resource facts and their unfolded authority should permit final certificate reuse"
    );
}

#[test]
fn parses_proof_tactic_script() {
    let source = FILL3_CLICK.replace("by auto;", "by { execute(); frame(loop(0)); simp(); }");
    let file = parse(&source).expect("explicit proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some(
            [
                ProofTactic::SmartExecute,
                ProofTactic::SmartFrame(Some(CodeRegionRef::Loop(0))),
                ProofTactic::Simp,
            ]
            .as_slice()
        )
    );
}

#[test]
fn parses_composite_resource_definition() {
    let source = r#"
            abstract resource socket_open(fd: int32);

            resource uncalled(flag: int32*) {
                contains socket_open(7);
                owns flag[0..1];
                fact flag[0] == 0;
            }
        "#;
    let file = parse(source).expect("composite resource should parse");
    let resource = &file.resource_definitions()[1];
    let composite_body = resource
        .composite_body()
        .expect("resource should have composite body");

    assert_eq!(resource.name(), "uncalled");
    assert_eq!(
        resource.parameters(),
        &[FunctionParameter {
            c_type: C0Type::Int32Pointer,
            name: "flag".to_string(),
            struct_name: None,
        }]
    );
    assert_eq!(
        composite_body.contains(),
        &[
            ResourceClause::Declared {
                access: ResourceAccessMode::Own,
                kind: ResourceKind::Token,
                name: "socket_open".to_string(),
                arguments: vec![current_int(7)],
                parameter_types: vec![C0Type::Int32],
            },
            ResourceClause::Write(ContractSegment {
                state: ContractSegmentState::Current,
                base: CExpression::Variable("flag".to_string()),
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(1)),
                surface: ContractSegmentSurface::Range {
                    base: current_var("flag"),
                    start: current_int(0),
                    end: current_int(1),
                },
            })
        ]
    );
    assert_eq!(composite_body.facts().len(), 1);
}

#[test]
fn parses_resource_observe_unfold_and_fold_tactics() {
    let source = r#"
            resource uncalled(flag: int32*) {
                owns flag[0..1];
            }

            verifying "identity.c";

            int32 identity(int32* flag) {
                owns uncalled(flag) by {
                    observe(uncalled(flag));
                    unfold(uncalled(flag));
                    execute();
                    fold(uncalled(flag));
                }
            }
        "#;
    let file = parse(source).expect("resource tactics should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some(
            [
                ProofTactic::ObserveResource(ResourceClause::Declared {
                    access: ResourceAccessMode::View,
                    kind: ResourceKind::Composite,
                    name: "uncalled".to_string(),
                    arguments: vec![current_var("flag")],
                    parameter_types: vec![C0Type::Int32Pointer],
                }),
                ProofTactic::UnfoldResource(ResourceClause::Declared {
                    access: ResourceAccessMode::Own,
                    kind: ResourceKind::Composite,
                    name: "uncalled".to_string(),
                    arguments: vec![current_var("flag")],
                    parameter_types: vec![C0Type::Int32Pointer],
                }),
                ProofTactic::SmartExecute,
                ProofTactic::FoldResource(ResourceClause::Declared {
                    access: ResourceAccessMode::Own,
                    kind: ResourceKind::Composite,
                    name: "uncalled".to_string(),
                    arguments: vec![current_var("flag")],
                    parameter_types: vec![C0Type::Int32Pointer],
                }),
            ]
            .as_slice()
        )
    );
}

#[test]
fn parses_resource_verb_function_clauses() {
    let source = r#"
            abstract resource socket_open(fd: int32);

            verifying "identity.c";

            int32 identity(int32* flag) {
                owns flag[0..1];
                views socket_open(7);
                consumes socket_open(8);
                produces socket_open(9);
            }
        "#;
    let file = parse(source).expect("resource verb clauses should parse");
    let function = &file.function_blocks()[0];

    assert_eq!(
        function.requires(),
        &[
            Requirement::Resource(ResourceClause::Write(ContractSegment {
                state: ContractSegmentState::Current,
                base: CExpression::Variable("flag".to_string()),
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(1)),
                surface: ContractSegmentSurface::Range {
                    base: current_var("flag"),
                    start: current_int(0),
                    end: current_int(1),
                },
            })),
            Requirement::Resource(ResourceClause::Declared {
                access: ResourceAccessMode::View,
                kind: ResourceKind::Token,
                name: "socket_open".to_string(),
                arguments: vec![current_int(7)],
                parameter_types: vec![C0Type::Int32],
            }),
            Requirement::Resource(ResourceClause::Declared {
                access: ResourceAccessMode::Own,
                kind: ResourceKind::Token,
                name: "socket_open".to_string(),
                arguments: vec![current_int(8)],
                parameter_types: vec![C0Type::Int32],
            }),
        ]
    );
    assert_eq!(
        function.ensures(),
        &[
            EnsureClause {
                name: None,
                ensure: Ensure::Resource(ResourceClause::Write(ContractSegment {
                    state: ContractSegmentState::Current,
                    base: CExpression::Variable("flag".to_string()),
                    start: CExpression::Value(int32(0)),
                    end: CExpression::Value(int32(1)),
                    surface: ContractSegmentSurface::Range {
                        base: current_var("flag"),
                        start: current_int(0),
                        end: current_int(1),
                    },
                })),
                proof: SourceProof::Default,
            },
            EnsureClause {
                name: None,
                ensure: Ensure::Resource(ResourceClause::Declared {
                    access: ResourceAccessMode::Own,
                    kind: ResourceKind::Token,
                    name: "socket_open".to_string(),
                    arguments: vec![current_int(9)],
                    parameter_types: vec![C0Type::Int32],
                }),
                proof: SourceProof::Default,
            },
        ]
    );
}

#[test]
fn parses_execute_proof_tactic() {
    let source = FILL3_CLICK.replace("by auto;", "by { execute(); }");
    let file = parse(&source).expect("execute proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some([ProofTactic::SmartExecute].as_slice())
    );
}

#[test]
fn parses_execute_and_simp_proof_tactics() {
    let source = FILL3_CLICK.replace("by auto;", "by { execute(); simp(); }");
    let file = parse(&source).expect("execute and simp proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some([ProofTactic::SmartExecute, ProofTactic::Simp].as_slice())
    );
}

#[test]
fn rejects_retired_tactic_forms_with_migrations() {
    for (form, replacement) in [
        ("conjunction", "split"),
        ("apply_loop_summary", "frontier-local"),
        ("summarize", "frontier-local"),
        ("execute_rest", "execute"),
        ("symbolic_execute", "execute"),
        ("execute_step", "step"),
        ("execute_then_step", "step"),
        ("execute_else_step", "step"),
        ("bounded_execute", "execute"),
        ("calculate", "simp() using"),
        ("double_negation", "intro"),
        ("vacuous", "intro"),
    ] {
        let source = format!("theorem legacy(x: int32) {{ ensures x == x by {{ {form}(); }} }}");
        let error = parse(&source).expect_err("retired tactic should be rejected");
        assert!(
            error.message().contains(replacement),
            "{form}: {}",
            error.message()
        );
    }
}

#[test]
fn rejects_redundant_exact_premise_forms_with_migrations() {
    let old_derive = r#"
        theorem legacy(x: int32) {
            requires x == x;
            ensures x == x by {
                derive(x == x) using {
                    x == x;
                }
            }
        }
    "#;
    let error = parse(old_derive).expect_err("removed derive tactic should be rejected");
    assert!(
        error.message().contains("unknown tactic `derive`"),
        "{}",
        error.message()
    );

    let old_fact_prefix = r#"
        theorem legacy(x: int32) {
            requires x == x;
            ensures x == x by {
                simp() using {
                    fact x == x;
                }
            }
        }
    "#;
    let error = parse(old_fact_prefix).expect_err("using fact prefix should be rejected");
    assert!(error.message().contains("redundant"), "{}", error.message());

    let old_step = FILL3_CLICK.replace("by auto;", "by { step using {} }");
    let error = parse(&old_step).expect_err("unparenthesized exact step should be rejected");
    assert!(
        error.message().contains("step() using"),
        "{}",
        error.message()
    );
}

#[test]
fn rejects_c_style_click_native_binders_with_migrations() {
    for source in [
        "predicate legacy(int32 x) { x == x }",
        "function legacy(int32 x) -> int32 { x }",
        "theorem legacy() { ensures forall (int32 k) { k == k } by auto; }",
        "theorem legacy() { ensures exists (int32 k) { k == k } by auto; }",
    ] {
        let error = parse(source).expect_err("C-style Click-native binder should be rejected");
        assert!(
            error.message().contains("name: type"),
            "{}",
            error.message()
        );
    }
}

#[test]
fn parses_smart_step_proof_tactic() {
    let source = FILL3_CLICK.replace("by auto;", "by { step(); execute(); simp(); }");
    let file = parse(&source).expect("smart step proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some(
            [
                ProofTactic::SmartStep,
                ProofTactic::SmartExecute,
                ProofTactic::Simp,
            ]
            .as_slice()
        )
    );
}
