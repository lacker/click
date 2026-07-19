use super::*;
use crate::kernel::int32;

#[test]
fn simp_uses_assumed_compound_proposition() {
    let proposition = Proposition::Or(
        Box::new(Proposition::Predicate {
            name: "left".to_string(),
            arguments: Vec::new(),
        }),
        Box::new(Proposition::Predicate {
            name: "right".to_string(),
            arguments: Vec::new(),
        }),
    );
    let assumptions = Assumptions::new().assume_proposition(proposition.clone());

    assert_eq!(
        simp_proposition(&proposition, &assumptions),
        SimpProposition::True
    );
}

const FILL3_C: &str = r#"
        int32 fill3(int32* p) {
            int32 i;
            i = 0;
            while (i < 3) {
                p[i] = i;
                i = i + 1;
            }
            return p[2];
        }
    "#;

const FILL3_CLICK: &str = r#"
        verifying "fill3.c";

        int32 fill3(int32* p) {
            requires loadable(p, 12);
            consumes p[0..3];
            ensures returns_second: result == 2 by auto;
        }
    "#;

fn current(expression: CExpression) -> ContractExpression {
    ContractExpression::CFragment(expression)
}

fn current_var(name: &str) -> ContractExpression {
    current(CExpression::Variable(name.to_string()))
}

fn current_int(value: u32) -> ContractExpression {
    current(CExpression::Value(int32(value)))
}

fn current_index(base: &str, index: u32) -> ContractExpression {
    ContractExpression::Index(Box::new(current_var(base)), Box::new(current_int(index)))
}

fn old_index(base: &str, index: u32) -> ContractExpression {
    ContractExpression::Old(Box::new(current_index(base, index)))
}

#[test]
fn executes_verified_loop_inside_selected_branch() {
    let c_source = r#"
        int32 branch_count_to_one(int32 flag, int32 i) {
            if (flag) {
                while (i < 1) {
                    i = i + 1;
                }
            } else {
                i = 1;
            }
            return i;
        }
    "#;
    let click_source = r#"
        verifying "branch_count_to_one.c";

        int32 branch_count_to_one(int32 flag, int32 i) {
            requires i == 1;
            requires flag != 0;

            for statement(0) {
                assert flag != 0 by auto;
            }

            for loop(0) as count {
                invariant i == 1;
            }

            ensures result == 1 by {
                execute_then_step();
                execute_step();
                have at(count.exit, i) == 1 by {
                    simp();
                }
                execute_step();
                simp();
            }
        }
    "#;

    verify_c0_sources(click_source, &[("branch_count_to_one.c", c_source)])
        .expect("branch-local loop execution should verify");
}

fn ensure_comparison(
    left: ContractExpression,
    operator: ComparisonOperator,
    right: ContractExpression,
) -> Ensure {
    Ensure::Proposition(ClickProposition::Comparison {
        left,
        operator,
        right,
    })
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
            Requirement::LoadableBytes {
                name: "p".to_string(),
                bytes: RangeBytes::Constant(12)
            },
            Requirement::Resource(ResourceClause::Write(ContractSegment {
                state: ContractSegmentState::Current,
                base: CExpression::Variable("p".to_string()),
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(3)),
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
}

#[test]
fn pure_simp_exposes_a_surface_derivation_certificate() {
    let source = r#"
        theorem positive_is_nonnegative(x: int32) {
            requires x > 0;
            ensures x >= 0 by simp;
        }
    "#;

    let verified = verify_click_theorems(source).expect("simp theorem should verify");
    assert!(matches!(
        verified[0].proof_tactics.as_deref(),
        Some([ProofTactic::Derive(ProofDerive { premises, .. })]) if premises.len() == 1
    ));
}

#[test]
fn verifies_explicit_structural_logic_tactics() {
    let source = r#"
        theorem conjunction_rule(x: int32) {
            requires x == x;
            ensures x == x and x == x by {
                conjunction();
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
                double_negation();
            }
        }

        theorem intro_implication_rule(x: int32) {
            ensures x == x implies x == x by {
                intro();
                assumption();
            }
        }

        theorem intro_forall_rule() {
            ensures forall (int32 k) { k == k } by {
                intro();
                normalize();
            }
        }

        theorem vacuous_rule(x: int32) {
            requires not (x != x);
            ensures x != x implies x == 0 by {
                vacuous();
            }
        }

        theorem contradiction_rule(x: int32) {
            requires x == 0;
            requires not (x == 0);
            ensures x == 1 by {
                contradiction(x == 0);
            }
        }
    "#;

    let verified = verify_click_theorems(source).expect("logical tactics should verify");
    assert_eq!(verified.len(), 8);
    assert!(verified.iter().all(|theorem| {
        theorem.proof_kind == ProofKind::TacticScript
            && theorem
                .proof_tactics
                .as_ref()
                .is_some_and(|tactics| TacticCertificate::from_proof_tactics(tactics).is_ok())
    }));
}

#[test]
fn verifies_atomic_derivation_from_explicit_premises() {
    let source = r#"
        theorem derives_nonnegative(x: int32) {
            requires x > 0;
            ensures x >= 0 by {
                derive(x >= 0) using {
                    fact x > 0;
                }
            }
        }

        theorem calculates_nonnegative(x: int32) {
            requires x > 0;
            ensures x >= 0 by {
                calculate(x >= 0) using {
                    fact x > 0;
                }
            }
        }
    "#;

    let verified = verify_click_theorems(source).expect("atomic derivations should verify");
    assert_eq!(verified.len(), 2);
    assert!(verified.iter().all(|theorem| {
        theorem
            .proof_tactics
            .as_ref()
            .is_some_and(|tactics| TacticCertificate::from_proof_tactics(tactics).is_ok())
    }));
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
        error.message().contains("different proposition"),
        "{}",
        error.message()
    );
}

#[test]
fn parses_symbolic_loadable_bytes() {
    let source = r#"
            verifying "fill.c";

            int32 fill(int32* p, int32 n) {
                requires loadable(p, n * 4);
                ensures result == n by auto;
            }
        "#;
    let file = parse(source).expect("symbolic loadable should parse");
    let function = &file.function_blocks()[0];

    assert_eq!(
        function.requires(),
        &[Requirement::LoadableBytes {
            name: "p".to_string(),
            bytes: RangeBytes::Multiply(
                Box::new(RangeBytes::Parameter("n".to_string())),
                Box::new(RangeBytes::Constant(4)),
            )
        }]
    );
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
            },
        }]
    );
}

#[test]
fn parses_loadable_segment_proposition() {
    let source = r#"
            verifying "read.c";

            predicate shifted_loadable(int32* p, int32 n) {
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

            predicate separated_backing(int32* p, int32* q, int32 n) {
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
            },
        }]
    );
    assert!(matches!(
        function.ensures()[0].ensure(),
        Ensure::Proposition(ClickProposition::Comparison { right, .. })
            if right == &ContractExpression::CFragment(
                CExpression::Load(Box::new(CExpression::Variable("obj".to_string())))
        )
    ));
}

#[test]
fn parses_pilot_struct_field_mutable_effect() {
    let source = r#"
            verifying "json_object_set_ref_count.c";

            int32 json_object_set_ref_count(struct json_object* obj, int32 count) {
                requires loadable(obj->ref_count);
                mutable_field(obj->ref_count) by frame;
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
        }])
    );
}

#[test]
fn parses_block_by_clause() {
    let source = FILL3_CLICK.replace("by auto;", "by { auto; }");
    let file = parse(&source).expect("sidecar should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert!(ensure.proof().is_auto_tactic());
}

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
                execute_rest();
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
                ProofTactic::ExecuteRest,
                ProofTactic::Frame(None),
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
                execute_rest();
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
                execute_rest();
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
        error.message().contains("last closing attempt:")
            && error.message().contains("missing pure fact:"),
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
                execute_rest();
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
        ProofTactic::ExecuteRest,
        ProofTactic::Frame(None),
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
fn omitted_region_proofs_use_default_prover() {
    let source = r#"
            verifying "count.c";

            int32 count() {
                for loop(0) {
                    invariant i >= 0;
                    mutable p[0..n];
                    step {
                        immutable;
                    }
                }

                ensures result == 3;
            }
        "#;
    let file = parse(source).expect("region proof clauses may be omitted");
    let function = &file.function_blocks()[0];
    let items = function.structural_clauses()[0].items();

    assert!(items[0].proof().is_auto_tactic());
    assert!(items[1].proof().is_auto_tactic());
    assert!(items[2].proof().is_auto_tactic());
    assert!(function.ensures()[0].proof().is_auto_tactic());
}

#[test]
fn parses_proof_tactic_script() {
    let source = FILL3_CLICK.replace("by auto;", "by { execute_rest(); frame(loop(0)); simp(); }");
    let file = parse(&source).expect("explicit proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some(
            [
                ProofTactic::ExecuteRest,
                ProofTactic::Frame(Some(CodeRegionRef::Loop(0))),
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
                    execute_rest();
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
                ProofTactic::ExecuteRest,
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
fn parses_bounded_execute_proof_tactic() {
    let source = FILL3_CLICK.replace("by auto;", "by { bounded_execute(); }");
    let file = parse(&source).expect("bounded explicit proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some([ProofTactic::BoundedExecute].as_slice())
    );
}

#[test]
fn parses_execute_rest_proof_tactic() {
    let source = FILL3_CLICK.replace("by auto;", "by { execute_rest(); simp(); }");
    let file = parse(&source).expect("execute_rest explicit proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some([ProofTactic::ExecuteRest, ProofTactic::Simp].as_slice())
    );
}

#[test]
fn parses_symbolic_execute_as_execute_rest() {
    let source = FILL3_CLICK.replace("by auto;", "by { symbolic_execute(); simp(); }");
    let file = parse(&source).expect("legacy alias should parse as execute_rest");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some([ProofTactic::ExecuteRest, ProofTactic::Simp].as_slice())
    );
}

#[test]
fn parses_execute_step_proof_tactic() {
    let source = FILL3_CLICK.replace("by auto;", "by { execute_step(); execute_rest(); simp(); }");
    let file = parse(&source).expect("execute_step explicit proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some(
            [
                ProofTactic::ExecuteStep,
                ProofTactic::ExecuteRest,
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

            predicate first_is_seven(int32 p[]) {
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
                transport(old(p[0]) == 7, p[0] == 7);
                step();
                frame();
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("transport.c", c_source)])
        .expect("explicit fact transport should verify");
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
    let first_value =
        Bitvector32Term::MemoryLoad(Box::new(base_memory.clone()), Box::new(first.clone()));
    let before_memory = base_memory
        .clone()
        .store(first.clone(), int32(first_value.clone()))
        .store(
            second.clone(),
            int32(Bitvector32Term::MemoryLoad(
                Box::new(base_memory.clone()),
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
    let statement = CStatement::Store {
        pointer: CExpression::Value(CValue::Pointer(second)),
        value: CExpression::Value(int32(9)),
    };
    let mut next_opaque_call = 0;
    let (transitions, _) = certified_statement_transitions(
        &state,
        std::slice::from_ref(&fact),
        &statement,
        &CExecutionEnvironment::new(),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        "simple transition test",
        &mut next_opaque_call,
        StatementPrerequisitePolicy::Exact,
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
                Box::new(post_state.memory().clone()),
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
                step();
                simp();
            }
        "#;

    let error = verify_c0_sources(click_source, &[("increment.c", c_source)])
        .expect_err("simple tactic must preserve the overflow prerequisite");
    assert!(
        error.message().contains("missing exact prerequisite"),
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
                step using {
                    fact x < 2147483647;
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
                execute_step();
                normalize();
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("increment.c", c_source)])
        .expect("the smart execution step should verify");
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the linear smart step should have a surface expansion");

    assert!(matches!(expanded[0], ProofTactic::StepUsing(_)));
    assert_eq!(expanded[1], ProofTactic::Normalize);
    assert_eq!(verified[0].expansion_blocker(), None);
    TacticCertificate::from_proof_tactics(expanded)
        .expect("the recorded expansion should be a surface certificate");
    let source = verified[0]
        .expanded_proof_source()
        .expect("checked expansion should have canonical source");
    assert!(source.contains("step using"));
    assert!(source.contains("normalize();"));
}

#[test]
fn execute_step_expands_atomic_snapshot_transport() {
    let c_source = r#"
            int32 set_second_return_first(int32 p[2]) {
                p[1] = 9;
                return p[0];
            }
        "#;
    let click_source = r#"
            verifying "transport.c";

            predicate first_is_seven(int32 p[]) {
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
                    execute_step();
                    execute_step();
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

    assert!(expanded.iter().any(|tactic| matches!(
        tactic,
        ProofTactic::Transport { source, target }
            if matches!(source, ClickProposition::Comparison { .. })
                && matches!(target, ClickProposition::Comparison { .. })
    )));
    TacticCertificate::from_proof_tactics(expanded)
        .expect("the transport expansion should be a surface certificate");
}

#[test]
fn parses_explicit_branch_execution_tactics() {
    let source = FILL3_CLICK.replace(
        "by auto;",
        "by { if n <= 0 { execute_then_step(); execute_rest(); simp(); } else { execute_else_step(); execute_rest(); simp(); } }",
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
        }) if then_tactics.first() == Some(&ProofTactic::ExecuteThenStep)
            && else_tactics.first() == Some(&ProofTactic::ExecuteElseStep)
    ));
}

#[test]
fn parses_advance_with_fact_and_resource_assertions() {
    let source = FILL3_CLICK.replace(
        "by auto;",
        r#"by {
            advance(statement(1).exit)
            ensuring {
                fact i >= 0;
                owns p[0..3];
                views p[0..3];
            }
            by {
                execute_step();
            }
            execute_rest();
            simp();
        }"#,
    );
    let file = parse(&source).expect("advance tactic should parse");
    let tactics = file.function_blocks()[0].ensures()[0]
        .proof()
        .tactics()
        .expect("expected tactics");

    assert!(matches!(
        &tactics[0],
        ProofTactic::Advance(ProofAdvance {
            target: ProgramPointRef {
                region: CodeRegionRef::Statement(1),
                kind: ProgramPointKind::Exit,
            },
            assertions,
            tactics,
        }) if matches!(assertions.as_slice(), [
            ProofAssertion::Fact(_),
            ProofAssertion::Resource(ResourceClause::Write(_)),
            ProofAssertion::Resource(ResourceClause::Read(_)),
        ]) && tactics == &[ProofTactic::ExecuteStep]
    ));
    assert_eq!(tactics[1..], [ProofTactic::ExecuteRest, ProofTactic::Simp]);
}

#[test]
fn parses_execute_until_proof_tactic() {
    let source = FILL3_CLICK.replace(
        "by auto;",
        "by { execute_until(statement(1)); execute_rest(); simp(); }",
    );
    let file = parse(&source).expect("execute_until explicit proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some(
            [
                ProofTactic::ExecuteUntil(CodeRegionRef::Statement(1)),
                ProofTactic::ExecuteRest,
                ProofTactic::Simp,
            ]
            .as_slice()
        )
    );
}

#[test]
fn parses_unfold_proof_tactic() {
    let source = FILL3_CLICK.replace("by auto;", "by { execute_rest(); unfold(sorted); simp(); }");
    let file = parse(&source).expect("unfold explicit proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some(
            [
                ProofTactic::ExecuteRest,
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
        "by { execute_rest(); apply(nonnegative(result)); simp(); }",
    );
    let file = parse(&source).expect("apply explicit proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some(
            [
                ProofTactic::ExecuteRest,
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
        ProofTactic::ExecuteStep.class(),
        TacticClass::Smart(SmartTacticKind::ExecuteStep)
    ));
    assert!(matches!(
        ProofTactic::Step.class(),
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
        ProofTactic::ApplyLoopSummary(CodeRegionRef::Loop(0)).class(),
        TacticClass::Simple(SimpleTactic::LoopSummaryTransition)
    ));
    assert!(matches!(
        ProofTactic::CertifiedStatementStep(Vec::new()).class(),
        TacticClass::Simple(SimpleTactic::CertifiedStatementTransition)
    ));
    assert!(matches!(
        ProofTactic::CertifiedLoopSummaryStep(Vec::new()).class(),
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
        ProofTactic::Frame(None).class(),
        TacticClass::Simple(SimpleTactic::Frame)
    ));
    assert!(matches!(
        ProofTactic::ContextualFrame.class(),
        TacticClass::Smart(SmartTacticKind::Frame)
    ));
    assert!(matches!(
        ProofTactic::CertifiedFrame(Vec::new()).class(),
        TacticClass::Simple(SimpleTactic::CertifiedFrame)
    ));
    assert!(matches!(
        ProofTactic::ExecuteThenStep.class(),
        TacticClass::Smart(SmartTacticKind::ExecuteThenStep)
    ));
    assert!(matches!(
        ProofTactic::ExecuteElseStep.class(),
        TacticClass::Smart(SmartTacticKind::ExecuteElseStep)
    ));
    assert!(matches!(
        ProofTactic::ExecuteRest.class(),
        TacticClass::Smart(SmartTacticKind::ExecuteRest)
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
        ProofTactic::StepUsing(vec![nonnegative.clone()]),
        ProofTactic::If(ProofIf {
            condition: nonnegative.clone(),
            then_tactics: vec![ProofTactic::Have(ProofHave {
                proposition: nonnegative.clone(),
                proof: Proof::Script(vec![ProofTactic::Derive(ProofDerive {
                    proposition: nonnegative.clone(),
                    premises: vec![nonnegative.clone()],
                })]),
            })],
            else_tactics: vec![ProofTactic::Normalize],
        }),
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
    let error =
        TacticCertificate::from_proof_tactics(&[ProofTactic::CertifiedStatementStep(Vec::new())])
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
    let tactics = [ProofTactic::Advance(ProofAdvance {
        target: ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Exit,
        },
        assertions: Vec::new(),
        tactics: vec![ProofTactic::If(ProofIf {
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
            CertificatePathSegment::AdvanceBody,
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
        "by { have n < 2147483647 by { simp(); } execute_rest(); simp(); }",
    );
    let file = parse(&source).expect("local have tactic should parse");
    let tactics = file.function_blocks()[0].ensures()[0]
        .proof()
        .tactics()
        .expect("expected tactics");

    assert!(matches!(
        &tactics[0],
        ProofTactic::Have(ProofHave {
            proof: Proof::Script(inner),
            ..
        }) if inner == &[ProofTactic::Simp]
    ));
    assert_eq!(
        &tactics[1..],
        &[ProofTactic::ExecuteRest, ProofTactic::Simp]
    );
}

#[test]
fn parses_proof_if_tactic() {
    let source = FILL3_CLICK.replace(
        "by auto;",
        "by { if n <= 0 { execute_rest(); simp(); } else { execute_rest(); simp(); } }",
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
        }) if then_tactics == &[ProofTactic::ExecuteRest, ProofTactic::Simp]
            && else_tactics == &[ProofTactic::ExecuteRest, ProofTactic::Simp]
    ));
}

#[test]
fn parses_existential_proof_tactics() {
    let source = FILL3_CLICK.replace(
        "by auto;",
        "by { execute_rest(); choose(k from requirement has_k); witness(j = k + 1); simp(); }",
    );
    let file = parse(&source).expect("existential explicit proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some(
            [
                ProofTactic::ExecuteRest,
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
                requires has_x: exists (int32 k) { k == x };
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
                requires loadable(p, 8);
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
fn parses_loop_invariants_and_statement_asserts() {
    let source = r#"
            verifying "count.c";

            int32 count() {
                for statement(2) as initialized {
                    assert i == 0 by auto;
                }

                for loop(0) as count_loop {
                    invariant i >= 0;
                    invariant i <= 3;
                    mutable p[0..n] by auto;
                    step {
                        immutable by auto;
                    }
                    initialize by simp;
                    preserve by {
                        execute_step();
                        execute_step();
                        simp();
                    }
                }

                ensures result == 3 by auto;
            }
        "#;
    let file = parse(source).expect("sidecar should parse");
    let function = &file.function_blocks()[0];

    assert_eq!(function.structural_clauses().len(), 2);
    assert_eq!(
        function.structural_clauses()[0].region(),
        &CodeRegion::Statement(2)
    );
    assert_eq!(
        function.structural_clauses()[0].label(),
        Some("initialized")
    );
    assert_eq!(
        function.structural_clauses()[0].items()[0].kind(),
        StructuralItemKind::Assert
    );
    assert_eq!(
        function.structural_clauses()[1].region(),
        &CodeRegion::Loop(0)
    );
    assert_eq!(function.structural_clauses()[1].label(), Some("count_loop"));
    assert_eq!(function.structural_clauses()[1].items().len(), 4);
    assert_eq!(
        function.structural_clauses()[1].items()[0].kind(),
        StructuralItemKind::Invariant
    );
    assert_eq!(
        function.structural_clauses()[1].items()[2].kind(),
        StructuralItemKind::Effect
    );
    assert!(matches!(
        function.structural_clauses()[1].items()[2].effect(),
        Some(Effect::Mutable(_))
    ));
    assert!(matches!(
        function.structural_clauses()[1].items()[3].effect(),
        Some(Effect::Immutable)
    ));
    assert_eq!(
        function.structural_clauses()[1].items()[3].kind(),
        StructuralItemKind::StepEffect
    );
    assert!(matches!(
        function.structural_clauses()[1].initialize_proof(),
        Some(Proof::Tactic(SmartTactic::Simp))
    ));
    assert!(matches!(
        function.structural_clauses()[1].preserve_proof(),
        Some(Proof::Script(tactics)) if tactics.len() == 3
    ));
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
    let source = FILL3_CLICK.replace("by auto;", "by { execute_rest(); frame(loop 0); }");
    let error = parse(&source).expect_err("legacy proof tactic region syntax should fail");

    assert!(
        error.message().contains("expected LParen"),
        "{}",
        error.message()
    );
}

#[test]
fn parses_click_proposition_syntax() {
    let source = r#"
            verifying "logic.c";

            predicate nonnegative(int32 x) {
                x >= 0
            }

            int32 logic(int32 x) {
                requires x >= 0 and x < 10;
                requires nonnegative(x);
                ensures bounded: result >= 0 and result < 10 by auto;
                ensures implication: result == x implies result >= 0 by auto;
                ensures named_predicate: nonnegative(result) by auto;
                ensures quantified: forall (int32 k) {
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
            function inc_with_let(int32 x) -> int32 {
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

            predicate nonnegative(int32 x) {
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
fn verifies_opaque_predicate_from_requirement() {
    let c_source = r#"
            int32 identity_pointer_fact(int32* p) {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "identity_pointer_fact.c";

            predicate sorted_pair(int32* p) {
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

#[test]
fn unfolds_predicate_requirement_to_prove_consequence() {
    let c_source = r#"
            int32 keep_pair(int32* p) {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "keep_pair.c";

            predicate sorted_pair(int32* p) {
                p[0] <= p[1]
            }

            int32 keep_pair(int32* p) {
                requires loadable(p, 8);
                requires sorted_pair(p);
                ensures consequence: p[0] <= p[1] by {
                    execute_rest();
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
                ProofTactic::ExecuteRest,
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

            predicate sorted_pair(int32* p) {
                p[0] <= p[1]
            }

            int32 compare_swap2(int32* p) {
                requires loadable(p, 8);
                consumes p[0..2];
                ensures sorted: sorted_pair(p) by {
                    execute_rest();
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

            predicate sorted(int32* p, int32 n) {
                forall (int32 i) {
                    forall (int32 j) {
                        0 <= i and 0 <= j and i < j and j < n implies p[i] <= p[j]
                    }
                }
            }

            int32 keep_sorted(int32* p, int32 n) {
                requires n >= 0;
                requires loadable(p[0..n]);
                requires sorted(p, n);
                ensures still_sorted: sorted(p, n) by {
                    execute_rest();
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
                ensures add_zero: result == x + 0 by simp;
                ensures prop_simp: result == x and not (result != x) by simp;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)])
        .expect("simp should prove local normalized postconditions");

    assert_eq!(verified.len(), 2);
    assert_eq!(verified[0].proof_kind(), ProofKind::Simp);
    assert_eq!(verified[1].proof_kind(), ProofKind::Simp);
}

#[test]
fn smart_simp_expansion_replays_as_surface_click() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x by simp;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)])
        .expect("smart simp should verify");
    let expanded = verified[0]
        .expanded_proof_source()
        .expect("smart simp should lower to surface tactics");
    let expanded_source = click_source.replacen("by simp;", &expanded, 1);
    verify_c0_sources(&expanded_source, &[("identity.c", c_source)])
        .expect("printed smart simp expansion should replay");
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
                ensures result == 1 or result == 2 by simp;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("choose.c", c_source)])
        .expect("branched smart simp should verify");
    let expanded = verified[0]
        .expanded_proof_source()
        .expect("branched smart simp should lower to surface tactics");
    let expanded_source = click_source.replacen("by simp;", &expanded, 1);
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
                ensures first: result == x by simp;
                ensures second: result == x + 0 by simp;
            }
        "#;

    let expanded = expand_c0_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Ensure(1),
    )
    .expect("selected smart proof should expand");
    assert_eq!(expanded.matches("by simp;").count(), 1);
    assert!(expanded.contains("ensures first: result == x by simp;"));
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
                execute_rest();
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
    assert!(!expanded.contains("execute_rest();"));
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
                mutable p[0..n] by frame;
            }
        "#;

    let expanded = expand_c0_claim_source(
        click_source,
        &[("write_in_bounds.c", c_source)],
        "write_in_bounds",
        CProofClaim::Effect(0),
    )
    .expect("contextual frame should expand");
    assert!(!expanded.contains("by frame;"));
    verify_c0_sources(&expanded, &[("write_in_bounds.c", c_source)])
        .expect("expanded contextual frame should re-verify");
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
                ensures result == x by simp;
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
fn source_expander_rejects_default_proofs_without_rewrite_spans() {
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
        CProofClaim::Ensure(0),
    )
    .expect_err("default proof has no source clause to replace");

    assert!(error.message().contains("uses a default proof"));
    assert!(error.message().contains("no source proof clause"));
}

#[test]
fn verifies_simple_postcondition_with_proof_tactics() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures returns_x: result == x by {
                    execute_rest();
                    simp();
                }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)])
        .expect("explicit proof script should prove simple postcondition");

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].proof_kind(), ProofKind::TacticScript);
}

#[test]
fn verifies_omitted_proof_with_default_prover() {
    let c_source = r#"
            int32 zero() {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "zero.c";

            int32 zero() {
                immutable;
                ensures returns_zero: result == 0;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("zero.c", c_source)])
        .expect("omitted proof clauses should use the default prover");

    assert_eq!(verified.len(), 2);
    assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
    assert_eq!(verified[1].proof_kind(), ProofKind::LoopVerification);
}

#[test]
fn verifies_mutable_effect_with_bounded_frame_tactics() {
    let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires loadable(p, 8);
                consumes p[1..2];
                mutable p[1..2] by {
                    bounded_execute();
                    frame();
                }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("write_second.c", c_source)])
        .expect("bounded frame tactics should prove mutable effect");
    let expected_tactics = [ProofTactic::BoundedExecute, ProofTactic::Frame(None)];

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].proof_kind(), ProofKind::TacticScript);
    assert_eq!(
        verified[0].proof_tactics(),
        Some(expected_tactics.as_slice())
    );
}

#[test]
fn bare_frame_tactic_rejects_ensure_claim() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures returns_x: result == x by {
                    execute_rest();
                    frame();
                }
            }
        "#;

    let error = verify_c0_sources(click_source, &[("identity.c", c_source)])
        .expect_err("bare frame tactic should not prove postconditions");

    assert!(
        error
            .message()
            .contains("`frame()` proves function-level effect claims"),
        "{}",
        error.message()
    );
}

#[test]
fn auto_certificate_replays_for_bounded_execution() {
    let c_source = r#"
            int32 fill3_array_loop(int32 p[3]) {
                int32 i;
                i = 0;
                while (i < 3) {
                    p[i] = i;
                    i = i + 1;
                }
                return p[2];
            }
        "#;
    let auto_click_source = r#"
            verifying "fill3_array_loop.c";

            int32 fill3_array_loop(int32 p[3]) {
                requires loadable(p, 12);
                consumes p[0..3];
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= 3;
                }
                ensures writes_third: p[2] == 2 by auto;
            }
        "#;

    let auto_verified = verify_c0_sources(auto_click_source, &[("fill3_array_loop.c", c_source)])
        .expect("bounded auto proof should verify");
    let expected_tactics = [ProofTactic::BoundedExecute, ProofTactic::Simp];

    assert_eq!(auto_verified.len(), 1);
    assert_eq!(auto_verified[0].proof_kind(), ProofKind::TacticScript);
    assert_eq!(
        auto_verified[0].proof_tactics(),
        Some(expected_tactics.as_slice())
    );

    let explicit_click_source = r#"
            verifying "fill3_array_loop.c";

            int32 fill3_array_loop(int32 p[3]) {
                requires loadable(p, 12);
                consumes p[0..3];
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= 3;
                }
                ensures writes_third: p[2] == 2 by {
                    bounded_execute();
                    simp();
                }
            }
        "#;

    let explicit_verified =
        verify_c0_sources(explicit_click_source, &[("fill3_array_loop.c", c_source)])
            .expect("bounded auto certificate should replay as explicit tactics");

    assert_eq!(explicit_verified.len(), 1);
    assert_eq!(explicit_verified[0].proof_kind(), ProofKind::TacticScript);
    assert_eq!(
        explicit_verified[0].proof_tactics(),
        Some(expected_tactics.as_slice())
    );
}

#[test]
fn simp_rejects_effect_clauses() {
    let c_source = r#"
            int32 zero() {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "zero.c";

            int32 zero() {
                immutable by simp;
                ensures returns_zero: result == 0 by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("zero.c", c_source)])
        .expect_err("simp should not prove effect clauses");

    assert!(
        error
            .message()
            .contains("`simp` does not prove effect clauses"),
        "{}",
        error.message()
    );
}

#[test]
fn simp_rejects_loop_backed_claims() {
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
                ensures returns_three: result == 3 by simp;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
        .expect_err("simp should not run loop verification");

    assert!(
        error
            .message()
            .contains("`simp` does not prove loop-backed claims"),
        "{}",
        error.message()
    );
}

#[test]
fn verifies_symbolic_result_expression() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures returns_argument: result == x by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)])
        .expect("identity sidecar should verify");

    assert_eq!(verified.len(), 1);
    assert_eq!(
        verified[0].ensure_clause().unwrap().ensure(),
        &ensure_comparison(
            current_var("result"),
            ComparisonOperator::Equal,
            current_var("x"),
        )
    );
}

#[test]
fn verifies_memory_postcondition() {
    let source = FILL3_CLICK.replace(
        "ensures returns_second: result == 2",
        "ensures third: p[2] == 2",
    );
    let verified = verify_c0_sources(&source, &[("fill3.c", FILL3_C)])
        .expect("fill3 memory postcondition should verify");

    assert_eq!(verified.len(), 1);
    assert_eq!(
        verified[0].ensure_clause().unwrap().ensure(),
        &ensure_comparison(
            current_index("p", 2),
            ComparisonOperator::Equal,
            current_int(2),
        )
    );
}

#[test]
fn verifies_old_memory_postcondition_for_unmodified_cell() {
    let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires loadable(p, 8);
                consumes p[1..2];
                ensures writes_second: p[1] == 9 by auto;
                ensures keeps_first: p[0] == old(p[0]) by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("write_second.c", c_source)])
        .expect("old memory postcondition should verify");

    assert_eq!(verified.len(), 2);
    assert_eq!(
        verified[1].ensure_clause().unwrap().ensure(),
        &ensure_comparison(
            current_index("p", 0),
            ComparisonOperator::Equal,
            old_index("p", 0),
        )
    );
}

#[test]
fn verifies_quantified_old_memory_postcondition() {
    let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires loadable(p, 8);
                consumes p[1..2];
                ensures keeps_first_cell: forall (int32 k) {
                    0 <= k and k < 1 implies p[k] == old(p[k])
                } by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("write_second.c", c_source)])
        .expect("unwritten segment should match old memory");

    assert_eq!(verified.len(), 1);
}

#[test]
fn separate_requirement_proves_symbolic_unwritten_read() {
    let c_source = r#"
            int32 write_i_read_j(int32 p[], int32 i, int32 j, int32 n) {
                p[i] = 9;
                return p[j];
            }
        "#;
    let click_source = r#"
            verifying "write_i_read_j.c";

            int32 write_i_read_j(int32 p[], int32 i, int32 j, int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires i >= 0;
                requires i < n;
                requires j >= 0;
                requires j < n;
                requires loadable(p[0..n]);
                consumes p[i..i + 1];
                views p[j..j + 1];
                requires separate(memory(p[i..i + 1]), memory(p[j..j + 1]));
                mutable p[i..i + 1] by frame;
                ensures keeps_j: result == old(p[j]) by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("write_i_read_j.c", c_source)])
        .expect("separate singleton ranges should prove symbolic unwritten read");

    assert_eq!(verified.len(), 2);
}

#[test]
fn contextual_frame_expands_to_surface_bounds_and_exact_frame() {
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
                requires loadable(p[0..n]);
                consumes p[0..n];
                mutable p[0..n] by frame;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("write_in_bounds.c", c_source)])
        .expect("contextual frame should verify");
    let theorem = verified
        .iter()
        .find(|theorem| theorem.proof_kind() == ProofKind::Frame)
        .expect("effect claim should use the frame proof");
    let expanded = theorem.expanded_proof_tactics().unwrap_or_else(|| {
        panic!(
            "contextual frame should have a surface expansion: {:?}",
            theorem.expansion_blocker()
        )
    });
    assert!(
        expanded
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::Have(_)))
    );
    assert_eq!(expanded.last(), Some(&ProofTactic::Frame(None)));
    TacticCertificate::from_proof_tactics(expanded)
        .expect("contextual frame expansion should be a surface certificate");
}

#[test]
fn contextual_frame_expands_independently_in_branch_leaves() {
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
            verifying "write_selected.c";

            int32 write_selected(int32 p[2], int32 flag) {
                consumes p[0..2];
                mutable p[0..2] by frame;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("write_selected.c", c_source)])
        .expect("branched contextual frame should verify");
    let theorem = verified
        .iter()
        .find(|theorem| theorem.proof_kind() == ProofKind::Frame)
        .expect("effect claim should use the frame proof");
    let expanded = theorem.expanded_proof_tactics().unwrap_or_else(|| {
        panic!(
            "branched contextual frame should expand: {:?}",
            theorem.expansion_blocker()
        )
    });
    let proof_if = expanded
        .iter()
        .find_map(|tactic| match tactic {
            ProofTactic::If(proof_if) => Some(proof_if),
            _ => None,
        })
        .expect("branched frame expansion should retain the branch");
    assert_eq!(
        proof_if.then_tactics.last(),
        Some(&ProofTactic::Frame(None))
    );
    assert_eq!(
        proof_if.else_tactics.last(),
        Some(&ProofTactic::Frame(None))
    );
    TacticCertificate::from_proof_tactics(expanded)
        .expect("branched frame expansion should be a surface certificate");
}

#[test]
fn quantified_old_memory_rejects_overwritten_cell() {
    let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires loadable(p, 8);
                consumes p[1..2];
                ensures keeps_second_cell: forall (int32 k) {
                    1 <= k and k < 2 implies p[k] == old(p[k])
                } by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("write_second.c", c_source)])
        .expect_err("overwritten segment should not match old memory");

    assert!(
        error.message().contains("missing pure fact")
            && error.message().contains("available pure facts")
            && error.message().contains("available resource facts"),
        "{}",
        error.message()
    );
}

#[test]
fn verifies_mutable_segment_effect() {
    let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires loadable(p, 8);
                consumes p[1..2];
                mutable p[1..2] by frame;
                mutable p[0..2] by frame;
                ensures returns_written: result == 9 by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("write_second.c", c_source)])
        .expect("write should stay inside declared segments");

    assert_eq!(verified.len(), 3);
    assert!(matches!(
        verified[0].effect_clause().unwrap().effect(),
        Effect::Mutable(_)
    ));
    assert_eq!(verified[0].proof_kind(), ProofKind::Frame);
    assert_eq!(verified[1].proof_kind(), ProofKind::Frame);
}

#[test]
fn verifies_shifted_loadable_and_mutable_segment() {
    let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires loadable((p + 1)[0..1]);
                consumes (p + 1)[0..1];
                mutable (p + 1)[0..1] by frame;
                ensures returns_written: result == 9 by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("write_second.c", c_source)])
        .expect("shifted loadable should prove access and frame");

    assert_eq!(verified.len(), 2);
    assert_eq!(verified[0].proof_kind(), ProofKind::Frame);
    assert_eq!(verified[1].proof_kind(), ProofKind::LoopVerification);
}

#[test]
fn frame_rejects_ensure_clause() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures returns_argument: result == x by frame;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("identity.c", c_source)])
        .expect_err("frame should not prove postconditions");

    assert!(
        error
            .message()
            .contains("`frame` only proves effect clauses"),
        "{}",
        error.message()
    );
}

#[test]
fn mutable_segment_rejects_write_outside_segment() {
    let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires loadable(p, 8);
                consumes p[1..2];
                mutable p[0..1] by auto;
                ensures returns_written: result == 9 by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("write_second.c", c_source)])
        .expect_err("write outside segment should fail");

    assert!(
        error.message().contains("outside the mutable footprint"),
        "{}",
        error.message()
    );
    assert!(
        error.message().contains("write to `p[1]`"),
        "{}",
        error.message()
    );
    assert!(
        error.message().contains("mutable segments: [p[0..1]]"),
        "{}",
        error.message()
    );
    assert!(
        error.message().contains("evaluated segments"),
        "{}",
        error.message()
    );
}

#[test]
fn immutable_rejects_external_memory_write() {
    let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires loadable(p, 8);
                consumes p[1..2];
                immutable by auto;
                ensures returns_written: result == 9 by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("write_second.c", c_source)])
        .expect_err("immutable should reject external memory writes");

    assert!(
        error.message().contains("outside the mutable footprint"),
        "{}",
        error.message()
    );
    assert!(
        error.message().contains("evaluated segments"),
        "{}",
        error.message()
    );
}

#[test]
fn immutable_allows_stack_local_writes() {
    let c_source = r#"
            int32 count_to_one() {
                int32 i;
                i = 0;
                i = i + 1;
                return i;
            }
        "#;
    let click_source = r#"
            verifying "count_to_one.c";

            int32 count_to_one() {
                immutable by frame;
                ensures returns_one: result == 1 by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("count_to_one.c", c_source)])
        .expect("stack-local writes should not count as external mutation");

    assert_eq!(verified.len(), 2);
    assert_eq!(verified[0].proof_kind(), ProofKind::Frame);
}

#[test]
fn old_memory_postcondition_fails_for_overwritten_cell() {
    let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires loadable(p, 8);
                consumes p[1..2];
                ensures keeps_second: p[1] == old(p[1]) by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("write_second.c", c_source)])
        .expect_err("old memory postcondition for overwritten cell should fail");

    assert!(
        error
            .message()
            .contains("left side evaluated to 9, right side evaluated to load(p[1])"),
        "{}",
        error.message()
    );
}

#[test]
fn verifies_loop_invariants_and_statement_assert() {
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
                for statement(2) {
                    assert i == 0 by auto;
                }

                for loop(0) {
                    invariant i >= 0;
                    invariant i <= 3;
                }

                ensures result == 3 by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
        .expect("loop invariants and statement assert should verify");

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
}

#[test]
fn verifies_old_memory_loop_invariant() {
    let c_source = r#"
            int32 fill_tail(int32 p[], int32 n) {
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
            verifying "fill_tail.c";

            int32 fill_tail(int32 p[], int32 n) {
                requires n >= 1 and n <= 2147483647;
                requires loadable(p, n * 4);
                consumes p[0..n];
                for loop(0) {
                    invariant i >= 1 and i <= n;
                    invariant p[0] == old(p[0]);
                }
                ensures frame_and_result: p[0] == old(p[0]) and result == n by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("fill_tail.c", c_source)])
        .expect("old memory loop invariant should verify");

    assert_eq!(verified.len(), 1);
}

#[test]
fn verifies_old_memory_loop_invariant_with_segment_bounds() {
    let c_source = r#"
            int32 fill_tail(int32 p[], int32 n) {
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
            verifying "fill_tail.c";

            int32 fill_tail(int32 p[], int32 n) {
                requires n >= 1 and n <= 2147483647;
                requires loadable(p[0..n]);
                consumes p[0..n];
                for loop(0) {
                    invariant i >= 1 and i <= n;
                    invariant forall (int32 k) {
                        0 <= k and k < 1 implies p[k] == old(p[k])
                    };
                }
                ensures frame_and_result: forall (int32 k) {
                    0 <= k and k < 1 implies p[k] == old(p[k])
                } and result == n by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("fill_tail.c", c_source)])
        .expect("old memory segment loop invariant should verify");

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
}

#[test]
fn verifies_symbolic_segment_loadable() {
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
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= n;
                }
                ensures returns_n: result == n by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
        .expect("segment loadable should verify symbolic pointer loop");

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
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
                requires loadable(p[0..n]);
                views p[0..n];

                ensures returns_loaded_value: result == p[index] by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("read_index.c", c_source)])
        .expect("loadable segment should prove indexed read loadability");

    assert_eq!(verified.len(), 1);
}

#[test]
fn verifies_symbolic_loop_mutable_segment() {
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
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= n;
                }
                mutable p[0..n] by auto;
                ensures returns_n: result == n by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
        .expect("symbolic pointer loop writes should stay inside segment");

    assert_eq!(verified.len(), 2);
    assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
}

#[test]
fn verifies_loop_level_mutable_segment() {
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
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= n;
                    mutable p[0..n] by auto;
                }
                ensures returns_n: result == n by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
        .expect("loop-level mutable segment should verify each iteration");

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
}

#[test]
fn verifies_loop_level_iteration_relative_mutable_segment() {
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
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= n;
                    step {
                        mutable p[i..i + 1] by frame;
                    }
                }
                ensures returns_n: result == n by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
        .expect("loop-level mutable segment should support one-cell iteration ranges");

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
}

#[test]
fn loop_whole_mutable_rejects_loop_modified_local_in_segment() {
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
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= n;
                    mutable p[i..i + 1] by frame;
                }
                ensures returns_n: result == n by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
        .expect_err("whole-loop mutable footprint should reject loop-modified locals");

    assert!(
        error.message().contains("whole-loop `mutable` segment"),
        "{}",
        error.message()
    );
    assert!(error.message().contains("`i`"), "{}", error.message());
    assert!(error.message().contains("step"), "{}", error.message());
}

#[test]
fn verifies_loop_level_growing_prefix_mutable_segment() {
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
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= n;
                    step {
                        mutable p[0..i + 1] by frame;
                    }
                }
                ensures returns_n: result == n by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
        .expect("loop-level frame should support growing prefix segments");

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
}

#[test]
fn verifies_loop_level_shifted_suffix_mutable_segment() {
    let c_source = r#"
            int32 fill_tail(int32 p[], int32 n) {
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
            verifying "fill_tail.c";

            int32 fill_tail(int32 p[], int32 n) {
                requires n >= 1;
                requires n <= 2147483647;
                requires loadable(p[0..n]);
                consumes p[0..n];
                for loop(0) {
                    invariant i >= 1;
                    invariant i <= n;
                    mutable p[1..n] by frame;
                }
                ensures returns_n: result == n by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("fill_tail.c", c_source)])
        .expect("loop-level frame should support shifted suffix segments");

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
}

#[test]
fn verifies_loop_level_multi_segment_mutable_footprint() {
    let c_source = r#"
            int32 fill_two(int32 p[], int32 q[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    p[i] = i;
                    q[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
    let click_source = r#"
            verifying "fill_two.c";

            int32 fill_two(int32 p[], int32 q[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires loadable(p[0..n]);
                requires loadable(q[0..n]);
                consumes p[0..n];
                consumes q[0..n];
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= n;
                    step {
                        mutable p[i..i + 1], q[i..i + 1] by frame;
                    }
                }
                ensures returns_n: result == n by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("fill_two.c", c_source)])
        .expect("loop-level frame should support multiple mutable segments");

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
}

#[test]
fn loop_level_mutable_segment_rejects_write_outside_segment() {
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
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= n;
                    mutable p[0..0] by auto;
                }
                ensures returns_n: result == n by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
        .expect_err("write outside loop mutable segment should fail");

    assert!(
        error.message().contains("loop 0 mutable 0"),
        "{}",
        error.message()
    );
    assert!(
        error.message().contains("outside the mutable footprint"),
        "{}",
        error.message()
    );
    assert!(
        error.message().contains("evaluated segments"),
        "{}",
        error.message()
    );
    assert!(
        error.message().contains("external writes"),
        "{}",
        error.message()
    );
    assert!(
        error.message().contains("declared effect"),
        "{}",
        error.message()
    );
}

#[test]
fn loop_level_immutable_rejects_external_memory_write() {
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
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= n;
                    immutable by auto;
                }
                ensures returns_n: result == n by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
        .expect_err("loop-level immutable should reject external writes");

    assert!(
        error.message().contains("loop 0 immutable 0"),
        "{}",
        error.message()
    );
    assert!(
        error.message().contains("outside the mutable footprint"),
        "{}",
        error.message()
    );
}

#[test]
fn loop_level_immutable_allows_stack_local_update() {
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
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= 3;
                    immutable by frame;
                }
                ensures returns_three: result == 3 by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
        .expect("loop-level immutable should allow stack-local updates");

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
}

#[test]
fn function_immutable_allows_nonwriting_loop_with_mutable_bound() {
    let c_source = r#"
            int32 count_pointer_bound(int32 p[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    i = i + 1;
                }
                return i;
            }
        "#;
    let click_source = r#"
            verifying "count_pointer_bound.c";

            int32 count_pointer_bound(int32 p[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires loadable(p[0..n]);
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= n;
                    mutable p[0..n] by frame;
                }
                immutable by frame;
                ensures returns_n: result == n by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("count_pointer_bound.c", c_source)])
        .expect("a mutable upper bound does not imply the loop actually writes memory");

    assert_eq!(verified.len(), 2);
    assert_eq!(verified[0].proof_kind(), ProofKind::Frame);
    assert_eq!(verified[1].proof_kind(), ProofKind::LoopVerification);
}

#[test]
fn function_mutable_uses_loop_effect_summary() {
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
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= n;
                    mutable p[0..n] by frame;
                }
                mutable p[0..n] by frame;
                ensures returns_n: result == n by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
        .expect("function-level mutable should consume loop effect summary");

    assert_eq!(verified.len(), 2);
    assert_eq!(verified[0].proof_kind(), ProofKind::Frame);
    assert_eq!(verified[1].proof_kind(), ProofKind::LoopVerification);
}

#[test]
fn function_mutable_rejects_loop_effect_outside_function_bound() {
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
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= n;
                    mutable p[0..n] by frame;
                }
                mutable p[0..0] by frame;
                ensures returns_n: result == n by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
        .expect_err("function-level mutable should reject a wider loop effect summary");

    assert!(
        error.message().contains("effect summary range"),
        "{}",
        error.message()
    );
    assert!(
        error.message().contains("outside the mutable footprint"),
        "{}",
        error.message()
    );
}

#[test]
fn function_mutable_accepts_shifted_loop_effect_subset() {
    let c_source = r#"
            int32 fill_tail(int32 p[], int32 n) {
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
            verifying "fill_tail.c";

            int32 fill_tail(int32 p[], int32 n) {
                requires n >= 1;
                requires n <= 2147483647;
                requires loadable(p[0..n]);
                consumes p[0..n];
                for loop(0) {
                    invariant i >= 1;
                    invariant i <= n;
                    mutable (p + 1)[0..n - 1] by frame;
                }
                mutable p[0..n] by frame;
                ensures returns_n: result == n by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("fill_tail.c", c_source)])
        .expect("function-level mutable should accept a shifted loop effect subset");

    assert_eq!(verified.len(), 2);
    assert_eq!(verified[0].proof_kind(), ProofKind::Frame);
    assert_eq!(verified[1].proof_kind(), ProofKind::LoopVerification);
}

#[test]
fn function_immutable_rejects_writing_loop_effect_summary() {
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
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= n;
                    mutable p[0..n] by frame;
                }
                immutable by frame;
                ensures returns_n: result == n by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
        .expect_err("function-level immutable should reject a writing loop effect summary");

    assert!(
        error.message().contains("effect summary range"),
        "{}",
        error.message()
    );
}

#[test]
fn structural_invariant_rejects_frame_tactic() {
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
                for loop(0) {
                    invariant i >= 0;
                    preserve by frame;
                }
                ensures returns_three: result == 3 by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
        .expect_err("frame should not prove invariants");

    assert!(
        error.message().contains("`preserve` must use"),
        "{}",
        error.message()
    );
}

#[test]
fn loop_initialize_rejects_execution_tactics() {
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
                for loop(0) {
                    invariant i >= 0;
                    initialize by {
                        execute_step();
                        simp();
                    }
                }
                ensures result == 1 by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("count_once.c", c_source)])
        .expect_err("initialization should not execute loop body statements");

    assert!(
        error.message().contains("`initialize`")
            && error.message().contains("is a pure proof")
            && error.message().contains("execute_step"),
        "{}",
        error.message()
    );
}

#[test]
fn loop_preserve_requires_one_complete_iteration() {
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
                for loop(0) {
                    invariant i >= 0;
                    preserve by {
                        execute_step();
                        simp();
                    }
                }
                ensures result == 1 by auto;
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
fn loop_preserve_non_execution_tactics_do_not_fall_back_to_auto() {
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
                for loop(0) {
                    invariant i >= 0;
                    preserve by {
                        simp();
                    }
                }
                ensures result == 1 by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("count_once.c", c_source)])
        .expect_err("an explicit preservation script should not fall back to auto");

    assert!(
        error
            .message()
            .contains("must execute exactly one complete loop-body iteration"),
        "{}",
        error.message()
    );
}

#[test]
fn loop_phase_proofs_can_unfold_invariant_predicates() {
    let c_source = r#"
            int32 loop_sorted_range_invariant(int32 p[3]) {
                int32 i;
                i = 0;
                while (i < 3) {
                    i = i + 1;
                }
                return i;
            }
        "#;
    let click_source = r#"
            verifying "loop_sorted_range_invariant.c";

            predicate sorted(int32 p[], int32 n) {
                sorted_range(p, 0, n)
            }

            predicate sorted_range(int32 p[], int32 lo, int32 hi) {
                forall (int32 i) {
                    forall (int32 j) {
                        0 <= i and 0 <= j and lo <= i and i < j and j < hi implies p[i] <= p[j]
                    }
                }
            }

            int32 loop_sorted_range_invariant(int32 p[3]) {
                requires loadable(p[0..3]);
                requires sorted(p, 3);
                for loop(0) {
                    invariant i >= 0 and i <= 3;
                    invariant sorted(p, 3);
                    initialize by {
                        unfold(sorted);
                        unfold(sorted_range);
                        simp();
                    }
                    preserve by {
                        unfold(sorted);
                        unfold(sorted_range);
                    }
                    immutable by frame;
                }
                ensures still_sorted: sorted(p, 3) by {
                    execute_rest();
                    frame(loop(0));
                    unfold(sorted);
                    unfold(sorted_range);
                    simp();
                }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("loop_sorted_range_invariant.c", c_source)])
        .expect("loop phase unfolding should verify");

    assert_eq!(verified.len(), 1);
}

#[test]
fn verifies_symbolic_copy_segment_invariant() {
    let c_source = r#"
            int32 copy_n(int32 dst[], int32 src[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    dst[i] = src[i];
                    i = i + 1;
                }
                return i;
            }
        "#;
    let click_source = r#"
            verifying "copy_n.c";

            int32 copy_n(int32 dst[], int32 src[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires loadable(dst[0..n]);
                requires loadable(src[0..n]);
                consumes dst[0..n];
                views src[0..n];
                requires separate(memory(dst[0..n]), memory(src[0..n]));
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= n;
                    invariant forall (int32 k) {
                        0 <= k and k < i implies dst[k] == old(src[k])
                    };
                    mutable dst[0..n] by auto;
                }
                ensures returns_n: result == n by auto;
                ensures source_unchanged: forall (int32 k) {
                    0 <= k and k < n implies src[k] == old(src[k])
                } by {
                    execute_rest();
                    frame(loop(0));
                    simp();
                }
                ensures copied_segment: forall (int32 k) {
                    0 <= k and k < n implies dst[k] == old(src[k])
                } by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("copy_n.c", c_source)])
        .expect("symbolic copy loop should prove copied segment invariant");

    assert_eq!(verified.len(), 3);
    assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
}

#[test]
fn auto_certificate_replays_for_loop_frame_claim() {
    let c_source = r#"
            int32 copy_n(int32 dst[], int32 src[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    dst[i] = src[i];
                    i = i + 1;
                }
                return i;
            }
        "#;
    let auto_click_source = r#"
            verifying "copy_n.c";

            int32 copy_n(int32 dst[], int32 src[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires loadable(dst[0..n]);
                requires loadable(src[0..n]);
                consumes dst[0..n];
                views src[0..n];
                requires separate(memory(dst[0..n]), memory(src[0..n]));
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= n;
                    invariant forall (int32 k) {
                        0 <= k and k < i implies dst[k] == old(src[k])
                    };
                    mutable dst[0..n] by auto;
                }
                ensures source_unchanged: forall (int32 k) {
                    0 <= k and k < n implies src[k] == old(src[k])
                } by auto;
            }
        "#;

    let auto_verified = verify_c0_sources(auto_click_source, &[("copy_n.c", c_source)])
        .expect("auto should prove the source-memory postcondition");
    let source_unchanged = auto_verified
        .iter()
        .find(|theorem| {
            theorem
                .ensure_clause()
                .and_then(EnsureClause::name)
                .is_some_and(|name| name == "source_unchanged")
        })
        .expect("source_unchanged theorem should be present");
    let expected_tactics = [
        ProofTactic::ExecuteRest,
        ProofTactic::Frame(Some(CodeRegionRef::Loop(0))),
        ProofTactic::Simp,
    ];

    assert_eq!(source_unchanged.proof_kind(), ProofKind::LoopVerification);
    assert_eq!(
        source_unchanged.proof_tactics(),
        Some(expected_tactics.as_slice())
    );

    let explicit_click_source = r#"
            verifying "copy_n.c";

            int32 copy_n(int32 dst[], int32 src[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires loadable(dst[0..n]);
                requires loadable(src[0..n]);
                consumes dst[0..n];
                views src[0..n];
                requires separate(memory(dst[0..n]), memory(src[0..n]));
                for loop(0) {
                    invariant i >= 0;
                    invariant i <= n;
                    invariant forall (int32 k) {
                        0 <= k and k < i implies dst[k] == old(src[k])
                    };
                    mutable dst[0..n] by auto;
                }
                ensures source_unchanged: forall (int32 k) {
                    0 <= k and k < n implies src[k] == old(src[k])
                } by {
                    execute_rest();
                    frame(loop(0));
                    simp();
                }
            }
        "#;

    let explicit_verified = verify_c0_sources(explicit_click_source, &[("copy_n.c", c_source)])
        .expect("auto certificate should replay as explicit tactics");

    assert_eq!(explicit_verified.len(), 1);
    assert_eq!(explicit_verified[0].proof_kind(), ProofKind::TacticScript);
    assert_eq!(
        explicit_verified[0].proof_tactics(),
        Some(expected_tactics.as_slice())
    );
}

#[test]
fn false_loop_invariant_fails() {
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
                for loop(0) {
                    invariant i < 3;
                }

                ensures result == 3 by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
        .expect_err("false loop invariant should fail");

    assert!(
        error.message().contains("loop 0 invariant 0 preservation"),
        "{}",
        error.message()
    );
}

#[test]
fn false_loop_invariant_initialization_fails() {
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
                for loop(0) {
                    invariant i == 1;
                }

                ensures result == 3 by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
        .expect_err("false loop invariant initialization should fail");

    assert!(
        error.message().contains("loop 0 invariant 0 entry"),
        "{}",
        error.message()
    );
}

#[test]
fn verifies_symbolic_increment_with_numeric_requirement() {
    let c_source = r#"
            int32 increment(int32 x) {
                return x + 1;
            }
        "#;
    let click_source = r#"
            verifying "increment.c";

            int32 increment(int32 x) {
                requires x < 2147483647;
                ensures increments: result == x + 1 by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("increment.c", c_source)])
        .expect("increment sidecar should verify");

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].specification.requires().len(), 1);
}

#[test]
fn symbolic_increment_without_numeric_requirement_fails() {
    let c_source = r#"
            int32 increment(int32 x) {
                return x + 1;
            }
        "#;
    let click_source = r#"
            verifying "increment.c";

            int32 increment(int32 x) {
                ensures increments: result == x + 1 by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("increment.c", c_source)])
        .expect_err("increment without overflow requirement should fail");

    assert!(
        error
            .message()
            .contains("undefined behavior: signed overflow"),
        "{}",
        error.message()
    );
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
                    execute_step();
                    step();
                    execute_step();
                    step();
                    execute_step();
                    step();
                    execute_step();
                    simp();
                }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("count_two.c", c_source)])
        .expect("small tactics should traverse concrete loop heads and iterations");

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].proof_kind(), ProofKind::TacticScript);
}

#[test]
fn apply_loop_summary_advances_one_verified_loop_transition() {
    let c_source = r#"
            int32 count_to_two() {
                int32 i;
                i = 0;
                while (i < 2) {
                    i = i + 1;
                }
                return i;
            }
        "#;
    let click_source = r#"
            verifying "count_to_two.c";

            int32 count_to_two() {
                for loop(0) {
                    invariant i >= 0 and i <= 2;
                    initialize by auto;
                    preserve by auto;
                }
                ensures returns_two: result == 2 by {
                    step();
                    step();
                    apply_loop_summary(loop(0));
                    step();
                    simp();
                }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("count_to_two.c", c_source)])
        .expect("the explicit loop-summary tactic should apply the verified loop rule");

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].proof_kind(), ProofKind::TacticScript);
}

#[test]
fn apply_loop_summary_using_limits_context_to_explicit_premises() {
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
                requires n >= 0;
                requires n <= 2147483647;
                for loop(0) {
                    invariant i >= 0 and i <= n;
                    initialize by auto;
                    preserve by auto;
                }
                ensures returns_n: result == n by {
                    step();
                    step();
                    apply_loop_summary(loop(0)) using {
                        fact n >= 0;
                        fact n <= 2147483647;
                    }
                    step();
                    simp();
                }
            }
        "#;

    verify_c0_sources(click_source, &[("count_to_n.c", c_source)])
        .expect("explicit premises should justify one loop-summary transition");
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
                    bounded_execute();
                    normalize();
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
        assert_eq!(proof_if.then_tactics.last(), Some(&ProofTactic::Normalize));
        assert_eq!(proof_if.else_tactics.last(), Some(&ProofTactic::Normalize));
        TacticCertificate::from_proof_tactics(expanded)
            .expect("bounded branch expansion should be a surface certificate");
    }
}

#[test]
fn verifies_fill3_c0_source_with_sidecar_specification() {
    let verified = verify_c0_sources(FILL3_CLICK, &[("fill3.c", FILL3_C)])
        .expect("fill3 sidecar should verify");

    assert_eq!(verified.len(), 1);
    let verified = &verified[0];
    let base = Pointer {
        block: EXTERNAL_ARGUMENT_MEMORY_BLOCK.into(),
        offset: scale_int32_offset(
            Bitvector32Term::Variable(Variable(POINTER_ARGUMENT_VARIABLE_BASE)),
            4,
        ),
    };
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
            },
        )]),
    );
    let initial_resources =
        ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(3),
        )));
    let final_memory = initial_memory
        .clone()
        .with_block("local:i", 4)
        .store(first, int32(0))
        .store(second, int32(1))
        .store(third, int32(2))
        .store(local_i, int32(3));

    assert_eq!(
        verified.specification.state(),
        &CState::new()
            .with_memory(initial_memory)
            .with_resource_context(initial_resources.clone())
    );
    assert_eq!(verified.specification.arguments(), &[c_pointer_value(base)]);
    assert_eq!(
        verified.specification.outcome(),
        &CFunctionOutcome::Return {
            value: int32(2),
            state: CState::new()
                .with_memory(final_memory)
                .with_resource_context(initial_resources),
        }
    );
    assert_eq!(
        implication_body(verified.theorem.proposition()),
        &Proposition::CFunctionSatisfiesSpecification {
            function: syntax::parse_function(FILL3_C)
                .expect("fill3 should parse")
                .to_kernel_function()
                .with_resource_summary(
                    vec![CResourceSpec::Write(CMemorySegment::new(
                        CExpression::Variable("p".to_string()),
                        CExpression::Value(int32(0)),
                        CExpression::Value(int32(3)),
                    ))],
                    Vec::new(),
                )
                .with_contract(
                    Vec::new(),
                    vec![SpecProposition::Comparison {
                        left: SpecExpression::CExpression(CExpression::Variable(
                            "result".to_string(),
                        )),
                        operator: CComparisonOperator::Equal,
                        right: SpecExpression::Value(int32(2)),
                    }],
                    vec![CMemorySegment::new(
                        CExpression::Variable("p".to_string()),
                        CExpression::Value(int32(0)),
                        CExpression::Value(int32(3)),
                    )],
                    vec![CFunctionContractClaim::new(
                        CFunctionContractClaimKey::Ensure(0),
                    )],
                    true,
                ),
            specification: verified.specification.clone(),
        }
    );
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
fn failed_ensure_reports_actual_return() {
    let source = FILL3_CLICK.replace("result == 2", "result == 3");
    let error =
        verify_c0_sources(&source, &[("fill3.c", FILL3_C)]).expect_err("wrong result should fail");

    assert!(
        error
            .message()
            .contains("left side evaluated to 2, right side evaluated to 3"),
        "{}",
        error.message()
    );
}

#[test]
fn failed_memory_postcondition_reports_loaded_value() {
    let source = FILL3_CLICK.replace(
        "ensures returns_second: result == 2",
        "ensures third: p[2] == 3",
    );
    let error = verify_c0_sources(&source, &[("fill3.c", FILL3_C)])
        .expect_err("wrong memory postcondition should fail");

    assert!(
        error
            .message()
            .contains("left side evaluated to 2, right side evaluated to 3"),
        "{}",
        error.message()
    );
}

#[test]
fn modular_call_snapshot_reports_missing_preserved_struct_bound() {
    let initialize_c = r#"
        struct pair {
            int32 pos;
            int32 len;
        };

        int32 initialize(struct pair* p, int32 length) {
            p->pos = 0;
            p->len = length;
            return 0;
        }
    "#;
    let disturb_c = r#"
        struct pair {
            int32 pos;
            int32 len;
        };

        int32 disturb(struct pair* q) {
            q->pos = 7;
            return 0;
        }
    "#;
    let read_c = r#"
        struct pair {
            int32 pos;
            int32 len;
        };

        int32 read(struct pair* p) {
            return p->pos;
        }
    "#;
    let pipeline_c = r#"
        struct pair {
            int32 pos;
            int32 len;
        };

        int32 pipeline(struct pair* p, struct pair* q, int32 length) {
            int32 ignored;
            int32 value;
            ignored = initialize(p, length);
            ignored = disturb(q);
            value = read(p);
            return value;
        }
    "#;
    let click_source = r#"
        verifying "initialize.c";
        verifying "disturb.c";
        verifying "read.c";
        verifying "pipeline.c";

        int32 initialize(struct pair* p, int32 length) {
            consumes p[0..2];
            mutable p[0..2];
            produces p[0..2];
            ensures p->pos == 0;
            ensures p->len == length;
            ensures result == 0;
        } by {
            execute_rest();
            frame();
            simp();
        }

        int32 disturb(struct pair* q) {
            consumes q[0..2];
            mutable q[0..1];
            produces q[0..2];
            ensures result == 0;
        } by {
            execute_rest();
            frame();
            simp();
        }

        int32 read(struct pair* p) {
            requires p->pos < p->len;
            views p[0..2];
            immutable;
            ensures result == p->pos by auto;
        }

        int32 pipeline(struct pair* p, struct pair* q, int32 length) {
            requires 1 <= length;
            requires separate(memory(p[0..2]), memory(q[0..2]));
            consumes p[0..2];
            consumes q[0..2];
            mutable p[0..2], q[0..1];
            produces p[0..2];
            produces q[0..2];
            ensures result == 0;
        } by {
            execute_rest();
            frame();
            simp();
        }
    "#;
    let error = verify_c0_sources(
        click_source,
        &[
            ("initialize.c", initialize_c),
            ("disturb.c", disturb_c),
            ("read.c", read_c),
            ("pipeline.c", pipeline_c),
        ],
    )
    .expect_err("the preserved struct bound is not yet derived across the disjoint call");

    assert!(
        error.message().contains("read precondition")
            && error.message().contains("missing prerequisite"),
        "{}",
        error.message()
    );
}
