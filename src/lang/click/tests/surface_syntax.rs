use super::*;

#[test]
fn parser_accepts_its_supported_parenthesis_depth() {
    let source = super::scaling_tests::theorem_with_parenthesized_requirement(
        parser::PARENTHESIS_NESTING_LIMIT,
    );
    parser::parse_file_items(&source).expect("supported parenthesis depth should parse");
}

#[test]
fn parser_rejects_excessive_parenthesis_depth_with_a_source_diagnostic() {
    let source = super::scaling_tests::theorem_with_parenthesized_requirement(
        parser::PARENTHESIS_NESTING_LIMIT + 1,
    );
    let error = parser::parse_file_items(&source)
        .expect_err("excessive parenthesis depth should be rejected before recursive parsing");
    assert!(
        error
            .message()
            .contains("parenthesis nesting exceeds Click's supported depth of 16"),
        "unexpected diagnostic: {}",
        error.message()
    );
}

#[test]
fn parser_preserves_mixed_grouped_proposition_and_contract_expression_syntax() {
    let source = r#"
        theorem mixed_parentheses(x: int32, y: int32) {
            requires (x < y) and ((x + 1) == y);
            ensures x == x by { assumption(); }
        }
    "#;
    parser::parse_file_items(source)
        .expect("mixed proposition and contract-expression parentheses should parse");
}

#[test]
fn parses_expanded_typed_loads_and_old_loadability() {
    let source = r#"
        int32 example(int32 owner[], int32 data[]) {
            ensures result == 0;
        } by {
            step() using {
                loadable(old(owner[0..6]));
                load_int32_pointer((owner + 2)) == data;
                separate(
                    memory(owner[0..6]),
                    memory(load_int32_pointer((owner + 2))[0..load_int32(owner)])
                );
            }
        }
    "#;
    let file = parser::parse(source).expect("expanded step syntax should parse");
    let SourceProof::Script(tactics) = file.function_blocks[0]
        .grouped_proof()
        .expect("example should have a grouped proof")
    else {
        panic!("expected a proof script");
    };
    let ProofTactic::StepUsing(premises) = &tactics[0] else {
        panic!("expected a step() using tactic");
    };
    assert!(matches!(
        &premises[0],
        ClickProposition::Loadable { segment }
            if segment.state == ContractSegmentState::Old
    ));
    assert_eq!(
        diagnostics::describe_click_proposition(&premises[0]),
        "loadable(old(owner[0..6]))"
    );
    assert!(matches!(
        &premises[1],
        ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::TypedLoad {
                value_type: CType::Int32Pointer,
                ..
            }),
            operator: ComparisonOperator::Equal,
            ..
        }
    ));
    assert!(matches!(&premises[2], ClickProposition::Separate { .. }));
}

#[test]
fn parses_checked_signature_and_contract_clauses() {
    let file = parse(FILL3_CLICK).expect("sidecar should parse");

    assert_eq!(file.verifying_sources(), &["fill3.c".to_string()]);
    assert_eq!(file.function_blocks().len(), 1);
    let function = &file.function_blocks()[0];
    assert_eq!(function.signature().return_type(), C0Type::Int32);
    assert_eq!(function.signature().name(), "fill3");
    assert_eq!(
        function.signature().parameters(),
        &[FunctionParameter {
            c_type: C0Type::Int32Pointer,
            name: "p".to_string(),
            struct_name: None,
        }]
    );
    assert_eq!(
        function.requires(),
        &[
            Requirement::LoadableSegment {
                segment: ContractSegment {
                    state: ContractSegmentState::Current,
                    base: CExpression::Variable("p".to_string()),
                    start: CExpression::Value(int32(0)),
                    end: CExpression::Value(int32(3)),
                    surface: ContractSegmentSurface::Range {
                        base: current_var("p"),
                        start: current_int(0),
                        end: current_int(3),
                    },
                },
            },
            Requirement::Resource(ResourceClause::Write(ContractSegment {
                state: ContractSegmentState::Current,
                base: CExpression::Variable("p".to_string()),
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(3)),
                surface: ContractSegmentSurface::Range {
                    base: current_var("p"),
                    start: current_int(0),
                    end: current_int(3),
                },
            }))
        ]
    );
    assert_eq!(function.ensures().len(), 1);
    let ensure = &function.ensures()[0];
    assert_eq!(ensure.name(), Some("returns_second"));
    assert_eq!(
        ensure.ensure(),
        &ensure_comparison(
            current_var("result"),
            ComparisonOperator::Equal,
            current_int(2),
        )
    );
    assert!(ensure.proof().is_auto_tactic());
}

#[test]
fn parses_void_c_function_contracts_without_a_result_binding() {
    let source = r#"
        verifying "destroy.c";

        void destroy(int32* value) {
            consumes value[0..1];
        } by {
            execute();
            simp();
        }
    "#;
    let file = parse(source).expect("void C contracts should parse");
    assert_eq!(
        file.function_blocks()[0].signature().return_type(),
        C0Type::Void
    );

    let error = verify_c0_sources(
        r#"
            verifying "destroy.c";
            void destroy(int32* value) {
                ensures result == 0;
            }
        "#,
        &[("destroy.c", "void destroy(int32* value) { return; }")],
    )
    .expect_err("void contracts must not expose `result`");
    assert!(
        error.message().contains("`result` is not available"),
        "unexpected error: {}",
        error.message()
    );
}

#[test]
fn parses_pure_theorem_definition() {
    let source = r#"
            theorem preserves_nonnegative(x: int32) {
                requires input_nonnegative: x >= 0;
                ensures output_nonnegative: x >= 0 by auto;
            }
        "#;

    let file = parse(source).expect("theorem should parse");
    assert_eq!(file.theorem_definitions().len(), 1);
    let theorem = &file.theorem_definitions()[0];
    assert_eq!(theorem.name(), "preserves_nonnegative");
    assert_eq!(
        theorem.parameters(),
        &[FunctionParameter {
            c_type: C0Type::Int32,
            name: "x".to_string(),
            struct_name: None,
        }]
    );
    assert_eq!(theorem.requires().len(), 1);
    assert_eq!(theorem.requires()[0].label(), Some("input_nonnegative"));
    assert_eq!(theorem.ensures().len(), 1);
    assert_eq!(theorem.ensures()[0].name(), Some("output_nonnegative"));
}

#[test]
fn parses_and_prints_pure_induction_tactics() {
    let source = r#"
        theorem induction_shape(n: int32) {
            requires n >= 0;
            ensures n == n by {
                induct(n) as ih;
                apply(ih(n - 1));
                simp();
            }
        }
    "#;
    let file = parse(source).expect("induction proof should parse");
    let SourceProof::Script(tactics) = file.theorem_definitions()[0].ensures()[0].proof() else {
        panic!("expected an explicit theorem proof");
    };
    assert!(matches!(
        &tactics[0],
        ProofTactic::Induct { parameter, hypothesis }
            if parameter == "n" && hypothesis == "ih"
    ));
    assert!(matches!(
        &tactics[1],
        ProofTactic::ApplyTheorem(application)
            if application.name == "ih" && application.arguments.len() == 1
    ));

    let printable = vec![
        tactics[0].clone(),
        ProofTactic::ApplyInduction {
            hypothesis: "ih".to_string(),
            argument: match &tactics[1] {
                ProofTactic::ApplyTheorem(application) => application.arguments[0].clone(),
                _ => unreachable!(),
            },
        },
        ProofTactic::CloseInduction,
    ];
    let printed = super::printing::format_partial_tactic_sequence(&printable);
    let reparsed = parse(&format!(
        "theorem induction_shape(n: int32) {{ requires n >= 0; ensures n == n by {{ {printed} }} }}"
    ))
    .expect("printed induction proof should parse");
    assert_eq!(
        reparsed.theorem_definitions()[0].ensures()[0].proof(),
        &SourceProof::Script(tactics.clone())
    );
}

#[test]
fn verifies_pure_theorem_definition() {
    let source = r#"
            theorem preserves_nonnegative(x: int32) {
                requires x >= 0;
                ensures x >= 0 by auto;
            }
        "#;

    let verified = verify_click_theorems(source).expect("theorem should verify");
    assert_eq!(verified.len(), 1);
    assert_eq!(
        verified[0].theorem_definition.name(),
        "preserves_nonnegative"
    );
    assert_eq!(verified[0].proof_kind, ProofKind::Pure);
    verified[0]
        .proof_certificate()
        .expect("default pure proof should commit a surface certificate");
}

#[test]
fn pure_bare_apply_builds_a_checked_proof_object_certificate() {
    let source = r#"
        theorem equality_symmetric(first: int32, second: int32) {
            requires first == second;
            ensures second == first by simp;
        }

        theorem use_equality_symmetric(first: int32, second: int32) {
            requires first == second;
            ensures second == first by {
                apply(equality_symmetric(first, second));
                assumption();
            }
        }

        theorem use_equality_from_conjunction(first: int32, second: int32) {
            requires (first == second) and (second == second);
            ensures second == first by {
                apply(equality_symmetric(first, second));
                assumption();
            }
        }
    "#;

    let verified = verify_click_theorems(source).expect("bare apply should verify");
    assert!(matches!(
        verified[1].proof_tactics().as_deref(),
        Some([
            ProofTactic::ApplyTheoremUsing { application, premises },
            ProofTactic::Assumption,
        ]) if application.name == "equality_symmetric" && premises.len() == 1
    ));
    assert!(matches!(
        verified[2].proof_tactics().as_deref(),
        Some([
            ProofTactic::ApplyTheoremUsing { application, premises },
            ProofTactic::Assumption,
        ]) if application.name == "equality_symmetric"
            && matches!(premises.as_slice(), [ClickProposition::Comparison { .. }])
    ));

    let explicit = source.replace(
        "apply(equality_symmetric(first, second));",
        "apply(equality_symmetric(first, second)) using { first == second; }",
    );
    verify_click_theorems(&explicit).expect("exported explicit steps should verify independently");

    let corrupted = source.replace(
        "apply(equality_symmetric(first, second));",
        "apply(equality_symmetric(first, second)) using {}",
    );
    let error = verify_click_theorems(&corrupted)
        .expect_err("an independently supplied certificate cannot omit its premise");
    assert!(error.message().contains("required exact fact"), "{error:?}");
}

#[test]
fn pure_simp_exposes_an_explicit_theorem_certificate() {
    let source = r#"
        theorem positive_is_nonnegative(x: int32) {
            requires x > 0;
            ensures x >= 0 by simp;
        }
    "#;

    let verified = verify_click_theorems(source).expect("simp theorem should verify");
    assert!(matches!(
        verified[0].proof_tactics().as_deref(),
        Some([
            ProofTactic::ApplyTheoremUsing { application, premises },
            ProofTactic::Assumption,
        ]) if application.name == "int32_strictly_positive_is_nonnegative"
            && premises.len() == 1
    ));
}

#[test]
fn pure_simp_after_unfold_exposes_an_explicit_certificate() {
    let source = r#"
        predicate equality_chain(x: int32, y: int32, z: int32) {
            x == y and y == z
        }

        theorem equality_transitive_after_unfold(x: int32, y: int32, z: int32) {
            requires equality_chain(x, y, z);
            ensures x == z by {
                unfold(equality_chain);
                simp();
            }
        }
    "#;

    let verified = verify_click_theorems(source).expect("unfolded simp theorem should verify");
    let tactics = verified[0]
        .proof_tactics()
        .expect("unfolded simp should commit a surface certificate");
    assert!(tactics.iter().any(
        |tactic| matches!(tactic, ProofTactic::UnfoldPredicate(name) if name == "equality_chain")
    ));
    assert!(
        tactics
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::Rewrite(_)))
    );
}

#[test]
fn branching_pure_simp_exposes_explicit_branch_certificates() {
    let source = r#"
        theorem equality_is_decidable(x: int32) {
            ensures x == 0 or not (x == 0) by {
                if x == 0 {
                    simp();
                } else {
                    simp();
                }
            }
        }
    "#;

    let verified = verify_click_theorems(source).expect("branching simp theorem should verify");
    let tactics = verified[0]
        .proof_tactics()
        .expect("branching simp should commit a surface certificate");
    let [ProofTactic::If(proof_if)] = tactics.as_slice() else {
        panic!("expected one explicit case split, got {tactics:?}");
    };
    assert!(!proof_if.then_tactics.is_empty());
    assert!(!proof_if.else_tactics.is_empty());
}

#[test]
fn verifies_explicit_structural_logic_tactics() {
    let source = r#"
        theorem conjunction_rule(x: int32) {
            requires x == x;
            ensures x == x and x == x by {
                split();
            }
        }

        theorem left_rule(x: int32) {
            requires x == x;
            ensures x == x or x != x by {
                left();
            }
        }

        theorem right_rule(x: int32) {
            requires x == x;
            ensures x != x or x == x by {
                right();
            }
        }

        theorem double_negation_rule(x: int32) {
            requires x == x;
            ensures not (not (x == x)) by {
                intro();
                contradiction(x == x);
            }
        }

        theorem intro_implication_rule(x: int32) {
            ensures x == x implies x == x by {
                intro();
                assumption();
            }
        }

        theorem intro_forall_rule() {
            ensures forall (k: int32) { k == k } by {
                intro();
                normalize();
            }
        }

        theorem vacuous_rule(x: int32) {
            requires not (x != x);
            ensures x != x implies x == 0 by {
                intro();
                contradiction(x != x);
            }
        }

        theorem contradiction_rule(x: int32) {
            requires x == 0;
            requires not (x == 0);
            ensures x == 1 by {
                contradiction(x == 0);
            }
        }

        theorem condition_polarity_contradiction_rule(x: int32, y: int32) {
            requires x < y;
            requires not (x < y);
            ensures x == 0 by {
                contradiction(x < y);
            }
        }
    "#;

    let verified = verify_click_theorems(source).expect("logical tactics should verify");
    assert_eq!(verified.len(), 9);
    assert!(verified.iter().all(|theorem| {
        theorem.proof_kind == ProofKind::TacticScript && theorem.proof_certificate().is_ok()
    }));
}

#[test]
fn verifies_atomic_derivation_from_explicit_premises() {
    let source = r#"
        theorem derives_nonnegative(x: int32) {
            requires 1 <= x;
            ensures 0 <= x by {
                simp() using {
                    1 <= x;
                }
            }
        }

        theorem calculates_nonnegative(x: int32) {
            requires 1 <= x;
            ensures 0 <= x by {
                simp() using {
                    1 <= x;
                }
            }
        }
    "#;

    let verified = verify_click_theorems(source).expect("atomic derivations should verify");
    assert_eq!(verified.len(), 2);
    assert!(
        verified
            .iter()
            .all(|theorem| { theorem.proof_certificate().is_ok() })
    );
}

#[test]
fn records_checked_surface_spellings_for_lowered_propositions() {
    let left = ClickProposition::Comparison {
        left: current_var("x"),
        operator: ComparisonOperator::GreaterThan,
        right: current_int(0),
    };
    let right = ClickProposition::Comparison {
        left: current_var("x"),
        operator: ComparisonOperator::LessThan,
        right: current_int(10),
    };
    let surface = ClickProposition::And(Box::new(left.clone()), Box::new(right.clone()));
    let values = BTreeMap::from([(
        "x".to_string(),
        CValue::Int32(Bitvector32Term::Variable(Variable(42))),
    )]);
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let mut lowerer = KernelPropositionLowerer::new(
        values,
        BTreeMap::new(),
        CMemory::new(),
        &predicates,
        &functions,
    );
    let kernel = lowerer
        .lower_requirement_proposition(&surface)
        .expect("surface proposition should lower");
    let Proposition::And(kernel_left, kernel_right) = &kernel else {
        panic!("expected conjunction lowering");
    };
    let mut spellings = SurfacePropositionMap::default();
    spellings
        .record_lowering(&surface, &kernel)
        .expect("matching logical structure should record");

    assert_eq!(spellings.surface(&kernel).unwrap(), &surface);
    assert_eq!(spellings.surface(kernel_left).unwrap(), &left);
    assert_eq!(spellings.surface(kernel_right).unwrap(), &right);
    assert!(
        spellings
            .surface(&Proposition::Not(kernel_left.clone()))
            .is_err()
    );

    assert_eq!(
        spellings
            .checked_surface(&kernel, |_| Ok(kernel.clone()))
            .expect("the same point lowering should remain usable"),
        surface
    );
    let error = spellings
        .checked_surface(&kernel, |_| Ok(kernel_left.as_ref().clone()))
        .expect_err("a spelling from another proof point must not be reused");
    assert!(
        error
            .message()
            .contains("none of the recorded Click spellings"),
        "{}",
        error.message()
    );
}

#[test]
fn surface_synthesis_qualifies_a_c_local_named_result() {
    let local = Bitvector32Term::Variable(Variable(42));
    let proposition = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(local.clone()),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        true,
    );
    let state = CState::new().with_local("result", CValue::Int32(local));

    let surface = synthesize_surface_proposition(&proposition, &[], &[], &state)
        .expect("the local comparison should have a surface spelling");
    let ClickProposition::Comparison { left, .. } = surface else {
        panic!("expected a comparison spelling");
    };
    assert_eq!(left, ContractExpression::CBinding("result".to_string()));
}

#[test]
fn surface_synthesis_omits_a_predicates_hidden_resource_state_argument() {
    let function = syntax::parse_function(
        r#"
            struct pool {
                int32 capacity;
            };
            void inspect(struct pool* pool) {}
        "#,
    )
    .expect("struct pointer parameter should parse");
    let pool = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let proposition = Proposition::Predicate {
        name: "valid_pool".to_string(),
        arguments: vec![
            Term::CState(CState::new()),
            Term::CValue(CValue::Pointer(pool.clone())),
        ],
    };

    let surface = synthesize_surface_proposition(
        &proposition,
        function.parameters(),
        &[CExpression::Value(CValue::Pointer(pool))],
        &CState::new(),
    )
    .expect("the hidden state should not need a surface spelling");
    assert_eq!(
        surface,
        ClickProposition::PredicateCall {
            name: "valid_pool".to_string(),
            arguments: vec![ContractExpression::CFragment(CExpression::Variable(
                "pool".to_string(),
            ))],
        }
    );
}

#[test]
fn surface_synthesis_prefers_struct_field_places_to_typed_loads() {
    let function = syntax::parse_function(
        r#"
            struct vector {
                int32 len;
                int32 cap;
                int32* data;
            };
            int32 vector_len(struct vector* owner) {
                return owner->len;
            }
        "#,
    )
    .expect("struct parameter layout should parse");
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let proposition = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(CMemory::new()),
                Box::new(owner.clone()),
            )),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        true,
    );
    let surface = synthesize_surface_proposition(
        &proposition,
        function.parameters(),
        &[CExpression::Value(CValue::Pointer(owner.clone()))],
        &CState::new(),
    )
    .expect("known struct field load should have a surface spelling");
    let ClickProposition::Comparison { left, .. } = surface else {
        panic!("expected a comparison spelling");
    };
    assert!(matches!(
        &left,
        ContractExpression::Field { field, .. } if field == "len"
    ));
    assert_eq!(describe_contract_expression(&left), "owner->len");

    let data_pointer = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(CMemory::new()),
        Box::new(owner.offset_by_bytes(8)),
    );
    let first_data_cell = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(data_pointer),
            byte_width: 4,
        },
    };
    let proposition = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(CMemory::new()),
                Box::new(first_data_cell),
            )),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        true,
    );
    let surface = synthesize_surface_proposition(
        &proposition,
        function.parameters(),
        &[CExpression::Value(CValue::Pointer(owner))],
        &CState::new(),
    )
    .expect("indexed pointer field load should have a surface spelling");
    let ClickProposition::Comparison { left, .. } = surface else {
        panic!("expected a comparison spelling");
    };
    assert_eq!(describe_contract_expression(&left), "owner->data[0]");
}

#[test]
fn proof_source_printing_preserves_proposition_precedence() {
    let comparison = |operator, value| ClickProposition::Comparison {
        left: current_var("x"),
        operator,
        right: current_int(value),
    };
    let proposition = ClickProposition::And(
        Box::new(ClickProposition::Or(
            Box::new(comparison(ComparisonOperator::Equal, 0)),
            Box::new(comparison(ComparisonOperator::Equal, 1)),
        )),
        Box::new(comparison(ComparisonOperator::LessThan, 2)),
    );
    let source = super::printing::format_partial_tactic_sequence(&[ProofTactic::Have(ProofHave {
        proposition,
        proof: SourceProof::Script(vec![ProofTactic::Assumption]),
    })]);

    assert!(
        source.contains("have (x == 0 or x == 1) and x < 2 by"),
        "{source}"
    );

    let quantified = ClickProposition::ForAll {
        c_type: C0Type::Int32,
        name: "k".to_string(),
        body: Box::new(ClickProposition::Implies(
            Box::new(ClickProposition::And(
                Box::new(comparison(ComparisonOperator::LessEqual, 0)),
                Box::new(comparison(ComparisonOperator::LessThan, 2)),
            )),
            Box::new(comparison(ComparisonOperator::Equal, 1)),
        )),
    };
    let source = super::printing::format_partial_tactic_sequence(&[ProofTactic::Have(ProofHave {
        proposition: quantified,
        proof: SourceProof::Script(vec![ProofTactic::Assumption]),
    })]);

    assert!(
        source.contains("forall (k: int32) { x <= 0 and x < 2 implies x == 1 }"),
        "{source}"
    );
    let proof_source =
        format!("int32 example(int32 x) {{ ensures result == x; }} by {{\n{source}\n}}");
    parser::parse(&proof_source).expect("printed quantified proof source should parse");
}

#[test]
fn empty_atomic_premise_derivation_cannot_hide_an_ambient_premise() {
    let target = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(Variable(42))),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        true,
    );
    let error = check_atomic_premise_derivation_goal(
        &target,
        Vec::new(),
        &target,
        std::slice::from_ref(&target),
    )
    .expect_err("a contextual derivation must retain an explicit premise");
    assert!(error.contains("at least one explicit premise"), "{error}");
}

#[test]
fn normalize_closes_context_free_quantified_contradictions() {
    let source = r#"
theorem impossible_interval() {
    ensures forall (k: int32) {
        0 <= k and k < 0 implies k == 7
    } by {
        normalize();
    }
}
"#;

    verify_c0_sources(source, &[])
        .expect("normalize should replay a context-free quantified derivation");
}

#[test]
fn retains_distinct_surface_spellings_for_the_same_kernel_fact() {
    let current = ClickProposition::Comparison {
        left: current_var("x"),
        operator: ComparisonOperator::Equal,
        right: current_int(1),
    };
    let snapshot = ClickProposition::Comparison {
        left: ContractExpression::At {
            selector: VisitSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Statement(5),
                kind: ProgramPointKind::Entry,
            }),
            expression: Box::new(current_var("x")),
        },
        operator: ComparisonOperator::Equal,
        right: current_int(1),
    };
    let kernel = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let wrong = Proposition::ConditionIs(ConditionTerm::Constant(false), true);
    let mut spellings = SurfacePropositionMap::default();
    spellings.record_lowering(&current, &kernel).unwrap();
    spellings.record_lowering(&snapshot, &kernel).unwrap();

    assert_eq!(spellings.surface(&kernel).unwrap(), &snapshot);
    assert_eq!(
        spellings
            .checked_surface(&kernel, |surface| {
                Ok(if surface == &current {
                    kernel.clone()
                } else {
                    wrong.clone()
                })
            })
            .unwrap(),
        current
    );
}

#[test]
fn recorded_surface_fact_resolves_only_one_available_kernel_fact() {
    let surface = ClickProposition::Comparison {
        left: current_var("x"),
        operator: ComparisonOperator::Equal,
        right: current_int(1),
    };
    let first = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let second = Proposition::ConditionIs(ConditionTerm::Constant(false), false);
    let mut spellings = SurfacePropositionMap::default();
    spellings.record_lowering(&surface, &first).unwrap();
    spellings.record_lowering(&surface, &second).unwrap();

    assert_eq!(
        spellings.available_kernel(&surface, std::slice::from_ref(&first)),
        Some(&first)
    );
    assert_eq!(spellings.available_kernel(&surface, &[first, second]), None);
}

#[test]
fn indexed_surface_resolution_ignores_unrelated_available_facts() {
    let surface = ClickProposition::Comparison {
        left: current_var("x"),
        operator: ComparisonOperator::Equal,
        right: current_int(1),
    };
    let target = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let mut spellings = SurfacePropositionMap::default();
    spellings.record_lowering(&surface, &target).unwrap();
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut available = std::collections::BTreeSet::from([target.clone()]);
            available.extend((0..size).map(|index| {
                Proposition::ConditionIs(ConditionTerm::Variable(Variable(95_000 + index)), true)
            }));
            let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
                spellings.available_kernel_matching(&surface, |kernel| available.contains(kernel))
            });
            assert_eq!(resolved, Some(&target));
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 1),
        "fixed indexed surface lookup should ignore unrelated facts: {samples:?}"
    );
}

#[test]
fn surface_lowering_map_forks_and_local_updates_scale_logarithmically() {
    fn indexed_pair(index: u32) -> (ClickProposition, Proposition) {
        (
            ClickProposition::Comparison {
                left: ContractExpression::CBinding(format!("x{index}")),
                operator: ComparisonOperator::Equal,
                right: current_int(index),
            },
            Proposition::ConditionIs(ConditionTerm::Variable(Variable(index.into())), true),
        )
    }

    for size in [16_u32, 64, 256, 1024, 4096] {
        let mut spellings = SurfacePropositionMap::default();
        for index in 0..size {
            let (surface, kernel) = indexed_pair(index);
            spellings.record_lowering(&surface, &kernel).unwrap();
        }
        let ancestor = spellings.clone();
        assert!(spellings.shares_persistent_storage_with(&ancestor));

        let (surface, kernel) = indexed_pair(size);
        let before = crate::persistent::persistent_node_allocations();
        spellings.record_lowering(&surface, &kernel).unwrap();
        let allocations = crate::persistent::persistent_node_allocations() - before;
        let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
        let allocation_bound = 8 * logarithmic_height + 16;
        assert!(
            allocations <= allocation_bound,
            "size {size} surface update allocated {allocations} map nodes (bound {allocation_bound})"
        );
        assert!(ancestor.surface(&kernel).is_err());
        assert_eq!(spellings.surface(&kernel).unwrap(), &surface);
    }
}

#[test]
fn rejects_byte_counting_loadable_syntax() {
    let source = r#"
            verifying "fill.c";

            int32 fill(int32* p, int32 n) {
                requires loadable(p, n * 4);
                ensures result == n by auto;
            }
        "#;
    let error = parse(source).expect_err("byte-counting loadable syntax should be retired");
    assert!(error.message().contains("expected"), "{error:?}");
}

#[test]
fn parses_loadable_segment_syntax() {
    let source = r#"
            verifying "fill.c";

            int32 fill(int32* p, int32 n) {
                requires loadable(p[0..n]);
                ensures result == n by auto;
            }
        "#;
    let file = parse(source).expect("segment loadable should parse");
    let function = &file.function_blocks()[0];

    assert_eq!(
        function.requires(),
        &[Requirement::LoadableSegment {
            segment: ContractSegment {
                state: ContractSegmentState::Current,
                base: CExpression::Variable("p".to_string()),
                start: CExpression::Value(int32(0)),
                end: CExpression::Variable("n".to_string()),
                surface: ContractSegmentSurface::Range {
                    base: current_var("p"),
                    start: current_int(0),
                    end: current_var("n"),
                },
            },
        }]
    );
}

#[test]
fn parses_loadable_pointer_base_segment() {
    let source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires loadable((p + 1)[0..1]);
                ensures result == 9 by auto;
            }
        "#;
    let file = parse(source).expect("pointer-base loadable should parse");
    let function = &file.function_blocks()[0];

    assert_eq!(
        function.requires(),
        &[Requirement::LoadableSegment {
            segment: ContractSegment {
                state: ContractSegmentState::Current,
                base: CExpression::Add(
                    Box::new(CExpression::Variable("p".to_string())),
                    Box::new(CExpression::Value(int32(1))),
                ),
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(1)),
                surface: ContractSegmentSurface::Range {
                    base: ContractExpression::Add(
                        Box::new(current_var("p")),
                        Box::new(current_int(1)),
                    ),
                    start: current_int(0),
                    end: current_int(1),
                },
            },
        }]
    );
}

#[test]
fn parses_parenthesized_loaded_pointer_segment_base() {
    let source = r#"
            verifying "read.c";

            int32 read(int32* owner) {
                requires at(function.entry, loadable((load_int32_pointer((owner + 2)) + 0)[0..1]));
                ensures result == 0 by auto;
            }
        "#;

    parse(source).expect("a parenthesized loaded-pointer segment base should parse");
}

#[test]
fn parses_loadable_segment_proposition() {
    let source = r#"
            verifying "read.c";

            predicate shifted_loadable(p: int32*, n: int32) {
                loadable((p + 1)[0..n])
            }

            int32 read(int32* p, int32 n) {
                requires loadable((p + 1)[0..n]);
                requires shifted_loadable(p, n);
                ensures result == 0 by auto;
            }
        "#;
    let file = parse(source).expect("loadable proposition should parse");
    let function = &file.function_blocks()[0];

    assert_eq!(
        function.requires(),
        &[
            Requirement::LoadableSegment {
                segment: ContractSegment {
                    state: ContractSegmentState::Current,
                    base: CExpression::Add(
                        Box::new(CExpression::Variable("p".to_string())),
                        Box::new(CExpression::Value(int32(1))),
                    ),
                    start: CExpression::Value(int32(0)),
                    end: CExpression::Variable("n".to_string()),
                    surface: ContractSegmentSurface::Range {
                        base: ContractExpression::Add(
                            Box::new(current_var("p")),
                            Box::new(current_int(1)),
                        ),
                        start: current_int(0),
                        end: current_var("n"),
                    },
                },
            },
            Requirement::Proposition(ClickProposition::PredicateCall {
                name: "shifted_loadable".to_string(),
                arguments: vec![
                    ContractExpression::CFragment(CExpression::Variable("p".to_string())),
                    ContractExpression::CFragment(CExpression::Variable("n".to_string())),
                ],
            }),
        ]
    );
    assert!(matches!(
        file.predicate_definitions()[0].body(),
        ClickProposition::Loadable { .. }
    ));
}

#[test]
fn parses_resource_relation_propositions() {
    let source = r#"
            resource backing(p: int32*, n: int32) {
                owns p[0..n];
            }

            predicate separated_backing(p: int32*, q: int32*, n: int32) {
                separate(memory(p[0..n]), backing(q, n))
            }

            verifying "read.c";

            int32 read(int32* p, int32* q, int32 n) {
                requires contains(backing(p, n), memory(p[0..n]));
                requires separated_backing(p, q, n);
                ensures result == 0 by auto;
            }
        "#;
    let file = parse(source).expect("resource relation propositions should parse");
    let function = &file.function_blocks()[0];

    assert!(matches!(
        file.predicate_definitions()[0].body(),
        ClickProposition::Separate { .. }
    ));
    assert!(matches!(
        function.requires()[0],
        Requirement::Proposition(ClickProposition::Contains { .. })
    ));
    let Requirement::Proposition(ClickProposition::Contains { parent, .. }) =
        &function.requires()[0]
    else {
        panic!("expected contains proposition");
    };
    assert!(matches!(
        parent,
        ResourceSubject::Declared {
            kind: ResourceKind::Composite,
            parameter_types,
            ..
        } if parameter_types == &[C0Type::Int32Pointer, C0Type::Int32]
    ));
}

#[test]
fn parses_memory_separate_requirement() {
    let source = r#"
            verifying "copy.c";

            int32 copy(int32* dst, int32* src, int32 n) {
                requires separate(memory(dst[0..n]), memory(src[0..n]));
                ensures result == n by auto;
            }
        "#;
    let file = parse(source).expect("memory separation requirement should parse");
    let function = &file.function_blocks()[0];

    assert!(matches!(
        function.requires()[0],
        Requirement::Proposition(ClickProposition::Separate { .. })
    ));
}

#[test]
fn restricted_simp_premises_retain_declared_resource_argument_types() {
    let source = r#"
        resource wrapper(owner: int32*) {}

        int32 inspect(int32* owner) {
            ensures result == 0;
        } by {
            have separate(wrapper(owner), memory(owner[0..1])) by {
                simp() using {
                    separate(wrapper(owner), memory(owner[0..1]));
                }
            }
        }
    "#;
    let file = parse(source).expect("restricted simp resource premise should parse");
    let SourceProof::Script(tactics) = file.function_blocks()[0].grouped_proof().unwrap() else {
        panic!("expected grouped proof script");
    };
    let ProofTactic::Have(ProofHave {
        proof: SourceProof::Script(have_tactics),
        ..
    }) = &tactics[0]
    else {
        panic!("expected have proof");
    };
    let ProofTactic::SimpUsing(ProofSimpUsing { premises }) = &have_tactics[0] else {
        panic!("expected restricted simp");
    };
    assert!(matches!(
        &premises[0],
        ClickProposition::Separate {
            left: ResourceSubject::Declared { parameter_types, .. },
            ..
        } if parameter_types == &[C0Type::Int32Pointer]
    ));
}

#[test]
fn transport_using_retains_declared_resource_argument_types() {
    let source = r#"
        resource wrapper(owner: int32*) {}

        int32 inspect(int32* owner) {
            ensures result == 0;
        } by {
            have contains(wrapper(owner), memory(owner[0..1])) by {
                transport(
                    contains(wrapper(owner), memory(owner[0..1])),
                    contains(wrapper(owner), memory(owner[0..1]))
                ) using {
                    contains(wrapper(owner), memory(owner[0..1]));
                }
                assumption();
            }
        }
    "#;
    let file = parse(source).expect("transport resource premises should parse");
    let SourceProof::Script(tactics) = file.function_blocks()[0].grouped_proof().unwrap() else {
        panic!("expected grouped proof script");
    };
    let ProofTactic::Have(ProofHave {
        proof: SourceProof::Script(have_tactics),
        ..
    }) = &tactics[0]
    else {
        panic!("expected have proof");
    };
    let ProofTactic::TransportUsing {
        source,
        target,
        premises,
    } = &have_tactics[0]
    else {
        panic!("expected explicit transport");
    };
    for proposition in [source, target, &premises[0]] {
        assert!(matches!(
            proposition,
            ClickProposition::Contains {
                parent: ResourceSubject::Declared { parameter_types, .. },
                ..
            } if parameter_types == &[C0Type::Int32Pointer]
        ));
    }
}

#[test]
fn rejects_reversed_constant_loadable_segment() {
    let c_source = r#"
            int32 read_second(int32* p) {
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "read_second.c";

            int32 read_second(int32* p) {
                requires loadable(p[3..1]);
                ensures reads: result == p[1] by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("read_second.c", c_source)])
        .expect_err("reversed concrete segment should fail");

    assert!(
        error
            .message()
            .contains("`loadable` segment has an end before its start"),
        "{}",
        error.message()
    );
}

#[test]
fn parses_array_parameter_signature_as_pointer() {
    let source = FILL3_CLICK.replace("int32* p", "int32 p[3]");
    let file = parse(&source).expect("array parameter signature should parse");
    let function = &file.function_blocks()[0];

    assert_eq!(
        function.signature().parameters(),
        &[FunctionParameter {
            c_type: C0Type::Int32Pointer,
            name: "p".to_string(),
            struct_name: None,
        }]
    );
}

#[test]
fn parses_pilot_struct_pointer_signature_and_field_load() {
    let source = r#"
            verifying "json_object_ref_count.c";

            int32 json_object_get_ref_count(struct json_object* obj) {
                requires loadable(obj->ref_count);
                ensures returns_ref_count: result == obj->ref_count by auto;
                immutable by frame;
            }
        "#;
    let file = parse(source).expect("pilot struct pointer signature should parse");
    let function = &file.function_blocks()[0];

    assert_eq!(function.signature().return_type(), C0Type::Int32);
    assert_eq!(
        function.signature().parameters(),
        &[FunctionParameter {
            c_type: C0Type::Int32Pointer,
            name: "obj".to_string(),
            struct_name: Some("json_object".to_string()),
        }]
    );
    assert_eq!(
        function.requires(),
        &[Requirement::LoadableSegment {
            segment: ContractSegment {
                state: ContractSegmentState::Current,
                base: CExpression::Variable("obj".to_string()),
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(1)),
                surface: ContractSegmentSurface::Field("ref_count".to_string()),
            },
        }]
    );
    assert!(matches!(
        function.ensures()[0].ensure(),
        Ensure::Proposition(ClickProposition::Comparison { right, .. })
            if matches!(
                right,
                ContractExpression::Field { field, .. } if field == "ref_count"
            )
    ));
}

#[test]
fn parses_chained_struct_fields_with_imported_pointee_types() {
    let c_source = r#"
        struct leaf {
            int32 padding;
            int32 value;
        };
        struct node {
            int32 tag;
            struct leaf* child;
        };

        int32 read_nested(struct node* root) {
            return root->child->value;
        }
    "#;
    let click_source = r#"
        verifying "read_nested.c";

        int32 read_nested(struct node* root) {
            ensures result == root->child->value;
        } by {
            assumption();
        }
    "#;
    let file = parse_c0_click_file(click_source, &[("read_nested.c", c_source)])
        .expect("contract field chains should use imported struct pointee types");
    let Ensure::Proposition(ClickProposition::Comparison { right, .. }) =
        file.function_blocks()[0].ensures()[0].ensure()
    else {
        panic!("expected comparison ensure")
    };

    assert_eq!(
        super::diagnostics::describe_contract_expression(right),
        "root->child->value"
    );
    assert!(matches!(
        right,
        ContractExpression::Field {
            field,
            ..
        } if field == "value"
    ));
}

#[test]
fn nested_field_segments_keep_the_terminal_field_offset() {
    let c_source = r#"
        struct leaf {
            int32 padding;
            int32 value;
        };
        struct node {
            int32 tag;
            struct leaf* child;
        };

        int32 write_nested(struct node* root) {
            root->child->value = 7;
            return 7;
        }
    "#;
    let click_source = r#"
        verifying "write_nested.c";

        int32 write_nested(struct node* root) {
            views root->child;
            consumes root->child->value;
            mutable root->child->value;
            ensures result == 7;
        } by {
            execute();
            frame();
            simp();
        }
    "#;
    let file = parse_c0_click_file(click_source, &[("write_nested.c", c_source)])
        .expect("nested field segments should retain imported terminal field metadata");
    let Requirement::Resource(ResourceClause::Write(required)) =
        &file.function_blocks()[0].requires()[1]
    else {
        panic!("expected a nested owned field requirement")
    };
    let Effect::Mutable(segments) = file.function_blocks()[0].effects()[0].effect() else {
        panic!("expected a nested mutable field effect")
    };

    for segment in [required, &segments[0]] {
        assert_eq!(segment.start, CExpression::Value(int32(1)));
        assert_eq!(segment.end, CExpression::Value(int32(2)));
        assert!(matches!(
            segment.base,
            CExpression::TypedLoad {
                value_type: CType::Int32Pointer,
                ..
            }
        ));
    }

    verify_c0_sources(click_source, &[("write_nested.c", c_source)])
        .expect("the corrected nested segment should verify the write");
}

#[test]
fn parses_struct_object_segments_without_exposing_layout_cells() {
    let c_source = r#"
        struct vector {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 initialize(struct vector* owner) {
            return 0;
        }
    "#;
    let click_source = r#"
        verifying "initialize.c";

        int32 initialize(struct vector* owner) {
            requires loadable(owner->data[0..owner->cap]);
            consumes object(owner);
            produces object(owner);
            ensures separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        }
    "#;
    let file = parse_c0_click_file(click_source, &[("initialize.c", c_source)])
        .expect("whole struct objects should have a source-level segment spelling");
    let function = &file.function_blocks()[0];
    let Requirement::LoadableSegment { segment: range } = &function.requires()[0] else {
        panic!("expected a field-backed loadable range")
    };
    assert_eq!(
        super::diagnostics::describe_contract_segment(range),
        "owner->data[0..owner->cap]"
    );

    let Requirement::Resource(ResourceClause::Write(segment)) = &function.requires()[1] else {
        panic!("expected an owned object requirement")
    };

    assert_eq!(
        super::diagnostics::describe_contract_segment(segment),
        "object(owner)"
    );
    assert_eq!(segment.start, CExpression::Value(int32(0)));
    assert_eq!(segment.end, CExpression::Value(int32(4)));
    assert_eq!(
        segment.surface,
        ContractSegmentSurface::Object("vector".to_string())
    );
}

#[test]
fn parses_pilot_struct_field_mutable_effect() {
    let source = r#"
            verifying "json_object_set_ref_count.c";

            int32 json_object_set_ref_count(struct json_object* obj, int32 count) {
                requires loadable(obj->ref_count);
                mutable obj->ref_count by frame;
                ensures returns_count: result == count by auto;
            }
        "#;
    let file = parse(source).expect("pilot struct field effect should parse");
    let function = &file.function_blocks()[0];

    assert_eq!(
        function.effects()[0].effect(),
        &Effect::Mutable(vec![ContractSegment {
            state: ContractSegmentState::Current,
            base: CExpression::Variable("obj".to_string()),
            start: CExpression::Value(int32(0)),
            end: CExpression::Value(int32(1)),
            surface: ContractSegmentSurface::Field("ref_count".to_string()),
        }])
    );
}

#[test]
fn rejects_legacy_mutable_field_effect_spelling() {
    let source = r#"
            verifying "json_object_set_ref_count.c";

            int32 json_object_set_ref_count(struct json_object* obj, int32 count) {
                mutable_field(obj->ref_count) by frame;
                ensures returns_count: result == count by auto;
            }
        "#;
    let error = parse(source).expect_err("legacy mutable-field syntax should be retired");

    assert!(
        error.message().contains("expected `let`, `requires`"),
        "{}",
        error.message()
    );
}

#[test]
fn parses_block_by_clause() {
    let source = FILL3_CLICK.replace("by auto;", "by { auto; }");
    let file = parse(&source).expect("sidecar should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert!(ensure.proof().is_auto_tactic());
}
