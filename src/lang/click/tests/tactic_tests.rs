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
        function.grouped_proof().and_then(Proof::tactics),
        Some(
            [
                ProofTactic::SmartExecute,
                ProofTactic::SmartFrame(None),
                ProofTactic::Simp
            ]
            .as_slice()
        )
    );
    assert!(matches!(function.effects()[0].proof(), Proof::Default));
    assert!(matches!(function.ensures()[0].proof(), Proof::Default));
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
        error
            .message()
            .contains("grouped `simp` could not certify its complete claim transition"),
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
            resource socket_open(fd: int32);

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
            resource socket_open(fd: int32);

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
                proof: Proof::Default,
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
                proof: Proof::Default,
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
fn rejects_retired_tactic_spellings_with_migrations() {
    for (spelling, replacement) in [
        ("conjunction", "split"),
        ("apply_loop_summary", "frontier-local"),
        ("summarize", "frontier-local"),
        ("execute_rest", "execute"),
        ("symbolic_execute", "execute"),
        ("execute_step", "step"),
        ("execute_then_step", "step"),
        ("execute_else_step", "step"),
        ("bounded_execute", "execute"),
        ("calculate", "derive"),
        ("double_negation", "intro"),
        ("vacuous", "intro"),
    ] {
        let source =
            format!("theorem legacy(x: int32) {{ ensures x == x by {{ {spelling}(); }} }}");
        let error = parse(&source).expect_err("retired tactic should be rejected");
        assert!(
            error.message().contains(replacement),
            "{spelling}: {}",
            error.message()
        );
    }
}

#[test]
fn rejects_redundant_exact_premise_spellings_with_migrations() {
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
    let error = parse(old_derive).expect_err("derive target should be rejected");
    assert!(
        error.message().contains("derive using"),
        "{}",
        error.message()
    );

    let old_fact_prefix = r#"
        theorem legacy(x: int32) {
            requires x == x;
            ensures x == x by {
                derive using {
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

#[test]
fn simple_step_supports_explicit_fact_transport() {
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
                mutable p[1..2];
                produces p[0..2];
                ensures result == 7;
            } by {
                unfold(first_is_seven);
                step();
                transport(old(p[0]) == 7, p[0] == 7) using {
                    old(p[0]) == 7;
                }
                step();
                frame();
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("transport.c", c_source)])
        .expect("explicit fact transport should verify");

    let missing_source = click_source.replace(
        "transport(old(p[0]) == 7, p[0] == 7) using {
                    old(p[0]) == 7;
                }",
        "transport(old(p[0]) == 7, p[0] == 7) using {}",
    );
    let error = verify_c0_sources(&missing_source, &[("transport.c", c_source)])
        .expect_err("explicit transport must not borrow its logical source from ambient facts");
    assert!(
        error
            .message()
            .contains("requires a source derivable from its explicit facts"),
        "{}",
        error.message()
    );
}

#[test]
fn explicit_fact_transport_can_certify_a_derived_source() {
    let c_source = r#"
            int32 set_third_return_second(int32 p[3]) {
                p[2] = 9;
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "transport.c";

            predicate ordered(p: int32[]) {
                0 <= p[0] and p[0] <= p[1]
            }

            int32 set_third_return_second(int32 p[3]) {
                requires ordered(p);
                consumes p[0..3];
                mutable p[2..3];
                produces p[0..3];
                ensures result >= 0;
            } by {
                unfold(ordered);
                step();
                transport(0 <= old(p[1]), 0 <= p[1]);
                step();
                frame();
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("transport.c", c_source)])
        .expect("transport should certify a source derived from exact snapshot facts");
}

#[test]
fn clone_field_stores_with_observed_source_resource_verify() {
    let c_source = r#"
        struct cursor {
            int32 pos;
            int32 len;
            int32* data;
        };

        int32 clone_cursor(struct cursor* target, struct cursor* source) {
            target->pos = source->pos;
            target->len = source->len;
            target->data = source->data;
            return target->pos;
        }
    "#;
    let click_source = r#"
        resource readable(data: int32*, length: int32) {
            views data[0..length];
            fact 0 <= length;
        }

        resource cursor(owner: struct cursor*) {
            owns owner->pos;
            owns owner->len;
            owns owner->data;
            views readable(owner->data, owner->len);
            fact 0 <= owner->pos;
            fact owner->pos <= owner->len;
            fact separate(
                memory(owner[0..4]),
                memory(owner->data[0..owner->len])
            );
        }

        verifying "clone_cursor.c";

        int32 clone_cursor(struct cursor* target, struct cursor* source) {
            requires separate(memory(target[0..4]), memory(source[0..4]));
            requires separate(
                memory(target[0..4]),
                memory(source->data[0..source->len])
            );
            consumes target[0..4];
            views cursor(source);
            mutable target[0..4];
            ensures result == source->pos;
        } by {
            observe(cursor(source));
            step();
            step();
            step();
            step();
            frame();
            simp();
        }
    "#;

    verify_c0_sources(click_source, &[("clone_cursor.c", c_source)])
        .expect("clone field stores should verify");
}

#[test]
fn simple_statement_transition_does_not_transport_facts_automatically() {
    let base_memory = CMemory::new();
    let first = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let second = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let first_value = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(base_memory.clone()),
        Box::new(first.clone()),
    );
    let before_memory = base_memory
        .clone()
        .store(first.clone(), int32(first_value.clone()))
        .store(
            second.clone(),
            int32(Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(base_memory.clone()),
                Box::new(second.clone()),
            )),
        );
    let state = CState::new()
        .with_memory(before_memory)
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            CResourceFact::own_memory(CMemoryRange::new(
                first.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(2),
            )),
        ));
    let fact = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(first_value),
            Box::new(Bitvector32Term::Constant(7)),
        ),
        true,
    );
    let statement = CStatement::TypedStore {
        pointer: CExpression::Value(CValue::Pointer(second)),
        value: CExpression::Value(int32(9)),
        value_type: CType::Int32,
    };
    let mut next_opaque_call = 0;
    let mut next_verification_variable = 0;
    let (transitions, _) = certified_statement_transitions(
        &state,
        std::slice::from_ref(&fact),
        &statement,
        &CExecutionEnvironment::new(),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        "simple transition test",
        &mut next_opaque_call,
        &mut next_verification_variable,
        StatementPrerequisitePolicy::Explicit,
        StatementFactTransportPolicy::None,
        &[],
    )
    .expect("simple transition should execute");
    let [transition] = transitions.as_slice() else {
        panic!("expected one transition")
    };

    assert!(transition.pure_facts.contains(&fact));
    let CStatementOutcome::Normal(post_state) = &transition.outcome else {
        panic!("expected a normal transition")
    };
    let transported = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(post_state.memory().clone()),
                Box::new(first),
            )),
            Box::new(Bitvector32Term::Constant(7)),
        ),
        true,
    );
    assert!(!transition.pure_facts.contains(&transported));
}

#[test]
fn simple_step_does_not_contextually_prove_execution_prerequisites() {
    let c_source = r#"
            int32 increment(int32 x) {
                return x + 1;
            }
        "#;
    let click_source = r#"
            verifying "increment.c";

            int32 increment(int32 x) {
                requires x < 2147483647;
                ensures result > x;
            } by {
                step() using {
                }
                simp();
            }
        "#;

    let error = verify_c0_sources(click_source, &[("increment.c", c_source)])
        .expect_err("simple tactic must preserve the overflow prerequisite");
    assert!(
        error.message().contains("signed overflow"),
        "{}",
        error.message()
    );
}

#[test]
fn step_using_limits_execution_to_explicit_pure_premises() {
    let c_source = r#"
            int32 increment(int32 x) {
                return x + 1;
            }
        "#;
    let click_source = r#"
            verifying "increment.c";

            int32 increment(int32 x) {
                requires x < 2147483647;
                ensures result == x + 1;
            } by {
                step() using {
                    x < 2147483647;
                }
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("increment.c", c_source)])
        .expect("an explicit premise should justify one contextual execution transition");
}

#[test]
fn execute_step_records_a_point_checked_surface_expansion() {
    let c_source = r#"
            int32 increment(int32 x) {
                return x + 1;
            }
        "#;
    let click_source = r#"
            verifying "increment.c";

            int32 increment(int32 x) {
                requires x < 2147483647;
                ensures result == x + 1;
            } by {
                step();
                normalize();
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("increment.c", c_source)])
        .expect("the smart execution step should verify");
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the linear smart step should have a surface expansion");

    assert!(matches!(expanded[0], ProofTactic::StepUsing(_)));
    let ProofTactic::StepUsing(premises) = &expanded[0] else {
        unreachable!("the first expanded tactic was checked above")
    };
    assert_eq!(premises.len(), 1);
    assert_eq!(expanded[1], ProofTactic::Normalize);
    assert_eq!(verified[0].expansion_blocker(), None);
    TacticCertificate::from_proof_tactics(expanded)
        .expect("the recorded expansion should be a surface certificate");
    let source = verified[0]
        .expanded_proof_source()
        .expect("checked expansion should have canonical source");
    assert!(source.contains("step() using"));
    assert!(source.contains("normalize();"));

    let execute_offset = click_source
        .find("step()")
        .expect("proof should contain execute_step");
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
    let rewritten =
        expand_c0_tactic_source_at(click_source, &[("increment.c", c_source)], line, column)
            .expect("the overflow-safe step should expand");
    assert!(rewritten.contains("x < 2147483647;"), "{rewritten}");
    verify_c0_sources(&rewritten, &[("increment.c", c_source)])
        .expect("the emitted numeric prerequisite should replay");
}

#[test]
fn execute_rest_return_certificate_omits_unused_ambient_facts() {
    let c_source = r#"
            int32 return_x(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "return_x.c";

            int32 return_x(int32 x) {
                requires x < 100;
                ensures result == x;
            } by {
                execute();
                simp();
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("return_x.c", c_source)])
        .expect("the return proof should verify");
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the return proof should have a surface expansion");
    assert_eq!(expanded[0], ProofTactic::StepUsing(Vec::new()));
    assert!(matches!(expanded[1], ProofTactic::Have(_)));
    assert_eq!(expanded[2], ProofTactic::Assumption);

    let execute_offset = click_source
        .find("execute()")
        .expect("proof should contain execute_rest");
    let position = expansion::position_at_offset(click_source, execute_offset);
    let rewritten = expand_c0_tactic_source_at(
        click_source,
        &[("return_x.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the return execution should expand");
    assert!(rewritten.contains("    step() using {"), "{rewritten}");
    verify_c0_sources(&rewritten, &[("return_x.c", c_source)])
        .expect("the minimal return certificate should replay");
}

#[test]
fn execute_step_omits_materialization_only_transport() {
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
                    have p[0] == 7 by {
                        assumption();
                    }
                    step();
                    step();
                    frame();
                }
                produces p[0..2];
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("transport.c", c_source)])
        .expect("automatic snapshot transport should verify");
    let expanded = verified[0].expanded_proof_tactics().unwrap_or_else(|| {
        panic!(
            "atomic transport should have a surface expansion: {:?}",
            verified[0].expansion_blocker()
        )
    });

    assert!(
        !expanded
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::TransportUsing { .. })),
        "{expanded:#?}"
    );
    TacticCertificate::from_proof_tactics(expanded)
        .expect("the materialization-free expansion should be a surface certificate");
    let execute_offset = click_source
        .find("step()")
        .expect("proof should contain execute_step");
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
    let expanded_source =
        expand_c0_tactic_source_at(click_source, &[("transport.c", c_source)], line, column)
            .expect("the statement expansion should print as surface Click");
    assert!(!expanded_source.contains("transport("), "{expanded_source}");
    verify_c0_sources(&expanded_source, &[("transport.c", c_source)])
        .expect("the statement expansion should replay without representational transport");
}

#[test]
fn execute_step_omits_materialized_mixed_snapshot_transport() {
    let c_source = r#"
            int32 replace_first(int32 p[2]) {
                p[0] = 9;
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "transport.c";

            predicate first_less_than_second(p: int32[]) {
                p[0] < p[1]
            }

            int32 replace_first(int32 p[2]) {
                requires first_less_than_second(p);
                consumes p[0..2];
                mutable p[0..1] by {
                    unfold(first_less_than_second);
                    step();
                    step();
                    frame();
                }
                produces p[0..2];
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("transport.c", c_source)])
        .expect("mixed snapshot transport should verify");
    let expanded = verified[0].expanded_proof_tactics().unwrap_or_else(|| {
        panic!(
            "mixed snapshot transport should have a surface expansion: {:?}",
            verified[0].expansion_blocker()
        )
    });

    assert!(
        !expanded
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::TransportUsing { .. })),
        "{expanded:#?}"
    );
    TacticCertificate::from_proof_tactics(expanded)
        .expect("the mixed-snapshot expansion should be a surface certificate");
    let execute_offset = click_source
        .find("step()")
        .expect("proof should contain execute_step");
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
    let expanded_source =
        expand_c0_tactic_source_at(click_source, &[("transport.c", c_source)], line, column)
            .expect("the mixed-snapshot statement should expand");
    verify_c0_sources(&expanded_source, &[("transport.c", c_source)])
        .expect("the mixed-snapshot expansion should replay without representational transport");
}

#[test]
fn execute_step_omits_materialization_transport_across_statements() {
    let c_source = r#"
            int32 replace_first_then_touch_other(int32 p[2], int32 q[1]) {
                p[0] = 9;
                q[0] = 1;
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "transport.c";

            predicate first_less_than_second(p: int32[]) {
                p[0] < p[1]
            }

            int32 replace_first_then_touch_other(int32 p[2], int32 q[1]) {
                requires first_less_than_second(p);
                requires separate(memory(p[0..2]), memory(q[0..1]));
                consumes p[0..2];
                consumes q[0..1];
                mutable p[0..1], q[0..1] by {
                    unfold(first_less_than_second);
                    step();
                    step();
                    step();
                    frame();
                }
                produces p[0..2];
                produces q[0..1];
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("transport.c", c_source)])
        .expect("multi-statement snapshot transport should verify");
    let expanded = verified[0].expanded_proof_tactics().unwrap_or_else(|| {
        panic!(
            "multi-statement transport should have a surface expansion: {:?}",
            verified[0].expansion_blocker()
        )
    });

    assert_eq!(
        expanded
            .iter()
            .filter(|tactic| matches!(tactic, ProofTactic::TransportUsing { .. }))
            .count(),
        0,
        "{expanded:#?}"
    );
    TacticCertificate::from_proof_tactics(expanded)
        .expect("the multi-statement expansion should be a surface certificate");
    let execute_offset = click_source
        .find("step()")
        .expect("proof should contain execute_step");
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
    let expanded_source =
        expand_c0_tactic_source_at(click_source, &[("transport.c", c_source)], line, column)
            .expect("the first multi-statement step should expand");
    verify_c0_sources(&expanded_source, &[("transport.c", c_source)])
        .expect("the multi-statement expansion should replay without representational transport");
}

#[test]
fn execute_step_expands_call_assign_fact_from_internal_snapshot() {
    let increment_c_source = r#"
            int32 set_seven(int32 p[1]) {
                p[0] = 7;
                return 7;
            }
        "#;
    let caller_c_source = r#"
            int32 call_set_seven(int32 p[1]) {
                int32 result;
                result = set_seven(p);
                return result;
            }
        "#;
    let click_source = r#"
            verifying "set_seven.c";
            verifying "call_set_seven.c";

            int32 set_seven(int32 p[1]) {
                consumes p[0..1];
                mutable p[0..1];
                produces p[0..1];
                ensures result == 7;
                ensures p[0] == 7;
            } by {
                step();
                step();
                frame();
                simp();
            }

            int32 call_set_seven(int32 p[1]) {
                consumes p[0..1];
                mutable p[0..1];
                produces p[0..1];
                ensures result == 7;
                ensures p[0] == 7;
            } by {
                step();
                step();
                frame();
                simp();
            }
        "#;

    let caller_offset = click_source
        .find("int32 call_set_seven")
        .expect("caller should be present");
    let execute_offset = caller_offset
        + click_source[caller_offset..]
            .find("step()")
            .expect("caller should execute its call");
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

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[
            ("set_seven.c", increment_c_source),
            ("call_set_seven.c", caller_c_source),
        ],
        line,
        column,
    )
    .expect("call-assign facts should normalize to the source statement exit");
    assert!(expanded.contains("step() using {"), "{expanded}");
}

#[test]
fn synthesizes_pointer_offset_equality_as_pointer_comparison() {
    let owner_offset = PointerOffsetTerm::Int32Scaled {
        value: Box::new(Bitvector32Term::Variable(Variable(41))),
        byte_width: 4,
    };
    let data_offset = PointerOffsetTerm::Int32Scaled {
        value: Box::new(Bitvector32Term::Variable(Variable(42))),
        byte_width: 4,
    };
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: owner_offset,
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: data_offset.clone(),
    };
    let proposition = Proposition::ConditionIs(
        ConditionTerm::PointerOffsetEqual(
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(CMemory::new()),
                    Box::new(owner.clone()),
                )),
                byte_width: 4,
            }),
            Box::new(data_offset),
        ),
        true,
    );
    let parameters = [
        syntax::C0Parameter::new(C0Type::Int32Pointer, "owner".to_string(), None),
        syntax::C0Parameter::new(C0Type::Int32Pointer, "data".to_string(), None),
    ];
    let arguments = [
        CExpression::Value(CValue::Pointer(owner)),
        CExpression::Value(CValue::Pointer(data)),
    ];

    let surface = super::proof::synthesize_surface_proposition(
        &proposition,
        &parameters,
        &arguments,
        &CState::new(),
    )
    .expect("pointer-offset equality should have a Click spelling");

    assert!(matches!(
        surface,
        ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::TypedLoad {
                value_type: CType::Int32Pointer,
                ..
            }),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Variable(name)),
        } if name == "data"
    ));
}

#[test]
fn synthesizes_dynamically_indexed_pointer_offset_equality() {
    let owner_offset = PointerOffsetTerm::Int32Scaled {
        value: Box::new(Bitvector32Term::Variable(Variable(41))),
        byte_width: 4,
    };
    let data_offset = PointerOffsetTerm::Int32Scaled {
        value: Box::new(Bitvector32Term::Variable(Variable(42))),
        byte_width: 4,
    };
    let index = Bitvector32Term::Variable(Variable(43));
    let proposition = Proposition::ConditionIs(
        ConditionTerm::PointerOffsetEqual(
            Box::new(PointerOffsetTerm::Add(
                Box::new(data_offset.clone()),
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(index.clone()),
                    byte_width: 4,
                }),
            )),
            Box::new(PointerOffsetTerm::Add(
                Box::new(owner_offset.clone()),
                Box::new(PointerOffsetTerm::Constant(4)),
            )),
        ),
        true,
    );
    let parameters = [
        syntax::C0Parameter::new(C0Type::Int32Pointer, "owner".to_string(), None),
        syntax::C0Parameter::new(C0Type::Int32Pointer, "data".to_string(), None),
        syntax::C0Parameter::new(C0Type::Int32, "index".to_string(), None),
    ];
    let arguments = [
        CExpression::Value(CValue::Pointer(Pointer {
            block: "arg-memory".into(),
            offset: owner_offset,
        })),
        CExpression::Value(CValue::Pointer(Pointer {
            block: "arg-memory".into(),
            offset: data_offset,
        })),
        CExpression::Value(CValue::Int32(index)),
    ];

    let surface = super::proof::synthesize_surface_proposition(
        &proposition,
        &parameters,
        &arguments,
        &CState::new(),
    )
    .expect("dynamically indexed pointer equality should have a Click spelling");

    assert!(matches!(
        surface,
        ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Add(left, right)),
            operator: ComparisonOperator::Equal,
            ..
        } if matches!(left.as_ref(), CExpression::Variable(name) if name == "data")
            && matches!(right.as_ref(), CExpression::Variable(name) if name == "index")
    ));
}

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
