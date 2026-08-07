use super::diagnostics::describe_contract_expression;
use super::*;
use crate::kernel::int32;

#[test]
fn click_addition_cancels_a_negated_pointer_base() {
    let base = Bitvector32Term::Variable(Variable(90));
    let index = Bitvector32Term::Variable(Variable(91));
    let negative_base = Bitvector32Term::Subtract(
        Box::new(Bitvector32Term::Constant(0)),
        Box::new(base.clone()),
    );

    assert_eq!(
        super::lowering::bitvector32_add(
            negative_base,
            Bitvector32Term::Add(Box::new(base), Box::new(index.clone())),
        ),
        index
    );
}

#[test]
fn resource_neutral_callee_preserves_callers_allocation_resource() {
    let push_c = r#"
        struct vector {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 push(struct vector* owner, int32 value) {
            int32 index;
            int32* data;
            index = owner->len;
            data = owner->data;
            data[index] = value;
            owner->len = index + 1;
            return owner->len;
        }
    "#;
    let caller_c = r#"
        struct vector {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 caller(struct vector* owner, int32 value) {
            int32 pushed;
            pushed = push(owner, value);
            return pushed;
        }
    "#;
    let click_source = r#"
        resource storage(owner: struct vector*) {
            owns owner->len;
            owns owner->cap;
            owns owner->data;
            owns owner->data[0..owner->cap];
            fact 0 <= owner->len;
            fact owner->len <= owner->cap;
            fact loadable(owner->data[0..owner->len]);
            fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        }

        resource allocated(owner: struct vector*) {
            owns owner->len;
            owns owner->cap;
            owns owner->data;
            contains allocation(owner->data, owner->cap * 4);
            owns owner->data[0..owner->cap];
            fact 0 <= owner->len;
            fact owner->len <= owner->cap;
            fact 1 <= owner->cap;
            fact loadable(owner->data[0..owner->len]);
            fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
        }

        verifying "push.c";
        verifying "caller.c";

        int32 push(struct vector* owner, int32 value) {
            requires owner->len < owner->cap;
            owns storage(owner);
            mutable owner->len, owner->data[owner->len..owner->len + 1];
            ensures result == old(owner->len) + 1;
            ensures owner->len == old(owner->len) + 1;
            ensures 1 <= owner->len;
            ensures owner->cap == old(owner->cap);
            ensures owner->data == old(owner->data);
        } by {
            unfold(storage(owner));
            execute();
            fold(storage(owner));
            frame();
            simp();
        }

        int32 caller(struct vector* owner, int32 value) {
            requires owner->len < owner->cap;
            consumes allocated(owner);
            mutable owner->len, owner->data[owner->len..owner->len + 1];
            produces allocated(owner);
            ensures result == old(owner->len) + 1;
            ensures result == old(owner->len) + 1 or result == 0;
            ensures owner->len == old(owner->len) + 1;
        } by {
            unfold(allocated(owner));
            fold(storage(owner));
            execute_until(statement(2));
            unfold(storage(owner));
            have 1 <= owner->cap by simp;
            fold(allocated(owner));
            execute();
            frame();
            simp();
        }
    "#;

    verify_c0_sources(click_source, &[("push.c", push_c), ("caller.c", caller_c)])
        .expect("a storage-only callee should preserve its caller's allocation authority");
}

#[test]
fn exact_struct_field_offsets_remain_resolvable_after_deadline() {
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(100000))),
            byte_width: 4,
        },
    };
    let field = base.offset_by_bytes(4);

    let index = crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
        super::checking::pointer_element_index_from_base(&field, &base, &Assumptions::new())
    });

    assert_eq!(index, Some(Bitvector32Term::Constant(1)));
}

#[test]
fn verifier_diagnostics_are_bounded_deterministically_at_utf8_boundaries() {
    use std::cell::Cell;

    struct CountingDebug<'a>(&'a Cell<usize>);

    impl fmt::Debug for CountingDebug<'_> {
        fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            for _ in 0..10_000 {
                self.0.set(self.0.get() + 1);
                formatter.write_str("資源")?;
            }
            Ok(())
        }
    }

    let primary_cause = "owned_vector.grow path 2: ghost resource mismatch\n";
    let enormous = format!(
        "{primary_cause}{}",
        "資源".repeat(DEFAULT_DIAGNOSTIC_BYTE_LIMIT)
    );
    let first = super::diagnostics::bound_error_message_for_mode(enormous.clone(), false);
    let second = super::diagnostics::bound_error_message_for_mode(enormous.clone(), false);

    assert_eq!(first, second);
    assert!(first.starts_with(primary_cause));
    assert!(first.len() <= DEFAULT_DIAGNOSTIC_BYTE_LIMIT);
    assert!(first.contains("diagnostic truncated"));
    assert_eq!(
        super::diagnostics::bound_error_message_for_mode(enormous.clone(), true),
        enormous
    );

    let writes = Cell::new(0);
    let debug = super::diagnostics::bounded_debug_for_mode(&CountingDebug(&writes), false);
    assert!(
        writes.get() < 10_000,
        "bounded formatting must stop the producer"
    );
    assert!(debug.len() <= 2 * 1024);
    assert!(debug.contains("diagnostic truncated"));
}

#[test]
fn certificate_reconstruction_diagnostics_summarize_internal_snapshots() {
    let memory = CMemory::new().with_block("hidden-snapshot", 4);
    let fact = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory),
                Box::new(Pointer {
                    block: "hidden-snapshot".into(),
                    offset: PointerOffsetTerm::Constant(0),
                }),
            )),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        true,
    );
    let failures = (0..20)
        .map(|_| {
            (
                fact.clone(),
                ClickError::new(
                    "comparison fact has no replayable Surface Click spelling at this proof point",
                ),
            )
        })
        .collect::<Vec<_>>();

    let rendered = super::diagnostics::describe_unexpressed_pure_facts(&failures, &[], &[]);

    assert!(rendered.contains("int32 equality is true"), "{rendered}");
    assert!(
        rendered.contains("no replayable Surface Click spelling"),
        "{rendered}"
    );
    assert!(rendered.contains("8 more omitted"), "{rendered}");
    assert!(!rendered.contains("CMemory"), "{rendered}");
    assert!(!rendered.contains("hidden-snapshot"), "{rendered}");
}

#[test]
fn condition_certificate_search_reports_its_budget_without_dumping_snapshots() {
    let memory = CMemory::new().with_block("wide-hidden-snapshot", 256);
    let memory = crate::kernel::intern_c_memory(memory);
    let facts = (0u32..64)
        .map(|index| {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::MemoryLoad(
                        memory.clone(),
                        Box::new(Pointer {
                            block: "wide-hidden-snapshot".into(),
                            offset: PointerOffsetTerm::Constant(i64::from(index) * 4),
                        }),
                    )),
                    Box::new(Bitvector32Term::Constant(index)),
                ),
                true,
            )
        })
        .collect::<Vec<_>>();
    let goal = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(Variable(1))),
            Box::new(Bitvector32Term::Variable(Variable(2))),
        ),
        true,
    );
    let limits = crate::instrumentation::TacticLimits {
        simple: std::time::Duration::from_secs(1),
        smart: std::time::Duration::ZERO,
        control: std::time::Duration::from_secs(1),
    };
    let tactic = crate::instrumentation::TacticEvent {
        claim: "wide-condition.contract".to_string(),
        tactic_index: 0,
        tactic_name: "execute_until".to_string(),
        class: "smart".to_string(),
        statement_index: 0,
        source_index: 0,
    };

    let error = crate::instrumentation::with_tactic_limits(limits, || {
        crate::instrumentation::emit(crate::instrumentation::VerificationEvent::TacticStarted(
            tactic.clone(),
        ));
        let result = super::proof::search_condition_derivation(&goal, &facts)
            .expect_err("a zero smart budget should stop condition-certificate search");
        crate::instrumentation::emit(crate::instrumentation::VerificationEvent::TacticFailed(
            tactic,
        ));
        result
    });

    assert!(
        error
            .message()
            .contains("condition-certificate premise search exceeded"),
        "{error:?}"
    );
    assert!(
        error.message().contains("int32 equality is true"),
        "{error:?}"
    );
    assert!(
        error.message().contains("ambient condition facts: 64"),
        "{error:?}"
    );
    assert!(error.message().contains("exact premises"), "{error:?}");
    assert!(!error.message().contains("CMemory"), "{error:?}");
    assert!(
        !error.message().contains("wide-hidden-snapshot"),
        "{error:?}"
    );
}

#[test]
fn condition_certificate_search_is_not_sensitive_to_a_fact_prefix() {
    let mut facts = (0u32..64)
        .map(|index| {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Variable(Variable(100 + u64::from(index)))),
                    Box::new(Bitvector32Term::Constant(index)),
                ),
                true,
            )
        })
        .collect::<Vec<_>>();
    let left = Bitvector32Term::Variable(Variable(1));
    let middle = Bitvector32Term::Variable(Variable(2));
    let right = Bitvector32Term::Variable(Variable(3));
    facts.push(Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left.clone()), Box::new(middle.clone())),
        true,
    ));
    facts.push(Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(middle), Box::new(right.clone())),
        true,
    ));
    let goal = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
        true,
    );

    let derivation = super::proof::search_condition_derivation(&goal, &facts)
        .expect("condition search should remain within the verification budget")
        .expect("the two relevant facts should derive the goal even after 64 irrelevant facts");

    assert_eq!(derivation.context_premises().len(), 2);
    assert!(
        derivation.replay(&assumptions_from_propositions(&facts)),
        "the selected certificate premises must replay"
    );
}

#[test]
fn verifier_diagnostics_bound_fact_items_and_show_resource_deltas() {
    let facts = (0..20)
        .map(|index| {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Constant(index)),
                    Box::new(Bitvector32Term::Constant(index)),
                ),
                true,
            )
        })
        .collect::<Vec<_>>();
    let rendered = super::diagnostics::describe_pure_facts(&facts);
    assert!(rendered.contains("8 more omitted"), "{rendered}");

    let desired_resource = CResourceFact::own_composite(
        "owned_vector".to_string(),
        vec![CValue::Pointer(Pointer::null())],
    );
    let certified_resource = CResourceFact::own_composite(
        "allocation".to_string(),
        vec![CValue::Pointer(Pointer::null())],
    );
    let desired = CFunctionOutcome::Return {
        value: int32(0),
        state: CState::new()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(desired_resource)),
    };
    let certified = CFunctionOutcome::Return {
        value: int32(0),
        state: CState::new()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(certified_resource)),
    };
    let delta = super::diagnostics::describe_function_outcome_delta(&desired, &certified, &[], &[]);
    assert!(delta.contains("missing certified resources"), "{delta}");
    assert!(delta.contains("owned_vector"), "{delta}");
    assert!(delta.contains("extra certified resources"), "{delta}");
    assert!(delta.contains("allocation"), "{delta}");
    assert!(!delta.contains("CFunctionOutcome"), "{delta}");
}

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
            requires loadable(p[0..3]);
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

mod surface_syntax;
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

mod expansion_tests;

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
                    execute();
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
fn ordinary_verification_stops_at_the_tactic_deadline() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures returns_x: result == x by {
                    execute();
                    simp();
                }
            }
        "#;
    let limits = crate::instrumentation::TacticLimits {
        simple: std::time::Duration::ZERO,
        smart: std::time::Duration::ZERO,
        control: std::time::Duration::ZERO,
    };
    let (result, events) = crate::instrumentation::collect(|| {
        crate::instrumentation::with_tactic_limits(limits, || {
            verify_c0_sources(click_source, &[("identity.c", c_source)])
        })
    });
    let error = result.expect_err("the first tactic should hit its zero deadline");
    assert!(error.message().contains("time limit exceeded"), "{error:?}");
    let started = events
        .iter()
        .filter_map(|event| match event {
            crate::instrumentation::VerificationEvent::TacticStarted(tactic) => {
                Some(tactic.tactic_name.as_str())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        !started.is_empty(),
        "the interrupted tactic should be named"
    );
    assert!(
        !started.contains(&"simp"),
        "later tactics must not start after a deadline: {started:?}"
    );
}

#[test]
fn smart_frame_reports_its_deterministic_deadline() {
    let c_source = r#"
        int32 write_first(int32* data) {
            data[0] = 1;
            return 0;
        }
    "#;
    let click_source = r#"
        verifying "write_first.c";

        int32 write_first(int32* data) {
            consumes data[0..1];
            produces data[0..1];
            mutable data[0..1];
        } by {
            step() using { loadable(data[0..1]); }
            step() using {}
            frame();
            simp();
        }
    "#;
    let limits = crate::instrumentation::TacticLimits {
        simple: std::time::Duration::from_secs(1),
        smart: std::time::Duration::ZERO,
        control: std::time::Duration::from_secs(1),
    };

    let error = crate::instrumentation::with_tactic_limits(limits, || {
        verify_c0_sources(click_source, &[("write_first.c", c_source)])
    })
    .expect_err("smart frame should observe its zero tactic deadline");

    assert!(error.message().contains("time limit exceeded"), "{error:?}");
    assert!(error.message().contains("frame"), "{error:?}");
    assert!(
        error.message().contains("explicit simple tactics"),
        "{error:?}"
    );
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
    assert_eq!(verified[0].proof_kind(), ProofKind::TacticScript);
    assert_eq!(verified[1].proof_kind(), ProofKind::TacticScript);
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
                requires loadable(p[0..2]);
                consumes p[1..2];
                mutable p[1..2] by {
                    execute();
                    frame();
                }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("write_second.c", c_source)])
        .expect("bounded frame tactics should prove mutable effect");
    let expected_tactics = [ProofTactic::SmartExecute, ProofTactic::SmartFrame(None)];

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
                    execute();
                    frame();
                }
            }
        "#;

    let error = verify_c0_sources(click_source, &[("identity.c", c_source)])
        .expect_err("bare frame tactic should not prove postconditions");

    assert!(
        error
            .message()
            .contains("`frame` has no effect claim to prove"),
        "{}",
        error.message()
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
                requires loadable(p[0..2]);
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
                requires loadable(p[0..2]);
                consumes p[1..2];
                ensures keeps_first_cell: forall (k: int32) {
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
                mutable p[i..i + 1] by { execute(); frame(); }
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
            int32 write_in_bounds(int32 p[], int32 i, int32 n, int32* unrelated) {
                p[i] = 9;
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "write_in_bounds.c";

            int32 write_in_bounds(int32 p[], int32 i, int32 n, int32* unrelated) {
                requires n >= 0;
                requires n <= 2147483647;
                requires i >= 0;
                requires i < n;
                requires loadable(p[0..n]);
                requires loadable(unrelated[0..1]);
                consumes p[0..n];
                mutable p[0..n] by { execute(); frame(); }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("write_in_bounds.c", c_source)])
        .expect("contextual frame should verify");
    let theorem = verified
        .iter()
        .find(|theorem| theorem.effect_clause().is_some())
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
    let Some(ProofTactic::FrameUsing {
        region: None,
        premises,
    }) = expanded.last()
    else {
        panic!("contextual frame should end in exact frame replay: {expanded:?}");
    };
    assert!(
        !format!("{premises:?}").contains("unrelated"),
        "an irrelevant ambient loadability fact leaked into the exact frame certificate: {premises:?}"
    );
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
                mutable p[0..2] by { execute(); frame(); }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("write_selected.c", c_source)])
        .expect("branched contextual frame should verify");
    let theorem = verified
        .iter()
        .find(|theorem| theorem.effect_clause().is_some())
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
    assert!(matches!(
        proof_if.then_tactics.last(),
        Some(ProofTactic::FrameUsing { region: None, .. })
    ));
    assert!(matches!(
        proof_if.else_tactics.last(),
        Some(ProofTactic::FrameUsing { region: None, .. })
    ));
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
                requires loadable(p[0..2]);
                consumes p[1..2];
                ensures keeps_second_cell: forall (k: int32) {
                    1 <= k and k < 2 implies p[k] == old(p[k])
                } by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("write_second.c", c_source)])
        .expect_err("overwritten segment should not match old memory");

    assert!(
        error.message().contains("available pure facts")
            && error.message().contains("available resource facts"),
        "{}",
        error.message()
    );
    assert!(
        error.message().contains("unclosed goal:")
            && error.message().contains("p[k] == old(p[k])")
            && !error.message().contains("simplified:"),
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
                requires loadable(p[0..2]);
                consumes p[1..2];
                mutable p[1..2] by { execute(); frame(); }
                mutable p[0..2] by { execute(); frame(); }
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
    assert_eq!(verified[0].proof_kind(), ProofKind::TacticScript);
    assert_eq!(verified[1].proof_kind(), ProofKind::TacticScript);
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
                mutable (p + 1)[0..1] by { execute(); frame(); }
                ensures returns_written: result == 9 by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("write_second.c", c_source)])
        .expect("shifted loadable should prove access and frame");

    assert_eq!(verified.len(), 2);
    assert_eq!(verified[0].proof_kind(), ProofKind::TacticScript);
    assert_eq!(verified[1].proof_kind(), ProofKind::TacticScript);
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
                ensures returns_argument: result == x by { execute(); frame(); }
            }
        "#;

    let error = verify_c0_sources(click_source, &[("identity.c", c_source)])
        .expect_err("frame should not prove postconditions");

    assert!(
        error
            .message()
            .contains("`frame` has no effect claim to prove"),
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
                requires loadable(p[0..2]);
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
                requires loadable(p[0..2]);
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
                immutable by { execute(); frame(); }
                ensures returns_one: result == 1 by auto;
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("count_to_one.c", c_source)])
        .expect("stack-local writes should not count as external mutation");

    assert_eq!(verified.len(), 2);
    assert_eq!(verified[0].proof_kind(), ProofKind::TacticScript);
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
                requires loadable(p[0..2]);
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
        .and_then(Proof::tactics)
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
        .and_then(Proof::tactics)
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
fn uninitialized_scalar_read_fails_verification() {
    let c_source = r#"
            int32 read_uninitialized() {
                int32 x;
                return x;
            }
        "#;
    let click_source = r#"
            verifying "read_uninitialized.c";

            int32 read_uninitialized() {
                ensures result == 0 by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("read_uninitialized.c", c_source)])
        .expect_err("an uninitialized scalar read must not verify");
    assert!(
        error.message().contains("read of uninitialized storage"),
        "{}",
        error.message()
    );
}

#[test]
fn uninitialized_local_array_read_fails_verification() {
    let c_source = r#"
            int32 read_uninitialized_array() {
                int32 data[1];
                return data[0];
            }
        "#;
    let click_source = r#"
            verifying "read_uninitialized_array.c";

            int32 read_uninitialized_array() {
                ensures result == 0 by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("read_uninitialized_array.c", c_source)])
        .expect_err("an uninitialized local array read must not verify");
    assert!(
        error.message().contains("read of uninitialized storage"),
        "{}",
        error.message()
    );
}

#[test]
fn pointer_argument_keeps_its_null_execution_path() {
    let c_source = r#"
            int32 pointer_is_null(int32* p) {
                if (p == 0) {
                    return 1;
                }
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "pointer_is_null.c";

            int32 pointer_is_null(int32* p) {
                ensures result == 0 by auto;
            }
        "#;

    verify_c0_sources(click_source, &[("pointer_is_null.c", c_source)])
        .expect_err("an unconstrained pointer parameter may be null");
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
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
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
                    execute();
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
        block: PointerBlock::ExternalArgument,
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
        &Proposition::CFunctionPartiallySatisfiesSpecification {
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
                    vec![SpecProposition::MemoryLoadable {
                        memory: SpecMemory::Current,
                        base: SpecExpression::CExpression(CExpression::Variable("p".to_string(),)),
                        start: SpecExpression::Value(int32(0)),
                        end: SpecExpression::Value(int32(3)),
                        element_width: 4,
                    }],
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
                    vec![CFunctionContractClaim::ensure_proposition(0, 0)],
                    true,
                ),
            specification: verified.specification.clone(),
        }
    );
}

#[test]
fn bounded_auto_loop_expands_without_a_detached_summary() {
    let sources = [("fill3.c", FILL3_C)];
    let position = c0_tactic_source_position(FILL3_CLICK, &sources, "fill3.returns_second", 0)
        .expect("the default auto proof should have a source position");
    let expanded =
        expand_c0_tactic_source_at(FILL3_CLICK, &sources, position.line, position.column)
            .expect("bounded loop execution should have a surface certificate");

    assert!(!expanded.contains("summarize("), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the bounded loop certificate should freshly replay");
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
fn observed_cursor_facts_produce_replayable_surface_certificates() {
    let c_source = r#"
        struct input_cursor {
            int32 pos;
            int32 len;
            int32* data;
        };

        int32 input_cursor_peek(struct input_cursor* owner) {
            return owner->data[owner->pos];
        }
    "#;
    let take_c_source = r#"
        struct input_cursor {
            int32 pos;
            int32 len;
            int32* data;
        };

        int32 input_cursor_take(struct input_cursor* owner) {
            int32 value;
            value = owner->data[owner->pos];
            owner->pos = owner->pos + 1;
            return value;
        }
    "#;
    let click_source = r#"
        resource readable_input(data: int32*, length: int32) {
            views data[0..length];
            fact 0 <= length;
        }

        resource input_cursor(owner: struct input_cursor*) {
            owns owner->pos;
            owns owner->len;
            owns owner->data;
            views readable_input(owner->data, owner->len);
            fact 0 <= owner->pos;
            fact owner->pos <= owner->len;
            fact separate(
                memory(owner[0..4]),
                memory(owner->data[0..owner->len])
            );
        }

        verifying "input_cursor_peek.c";
        verifying "input_cursor_take.c";

        int32 input_cursor_peek(struct input_cursor* owner) {
            requires owner->pos < owner->len;
            views input_cursor(owner);
            immutable;
            ensures result == owner->data[owner->pos];
        } by {
            observe(input_cursor(owner));
            observe(readable_input(owner->data, owner->len));
            execute();
            frame();
            simp();
        }

        int32 input_cursor_take(struct input_cursor* owner) {
            requires owner->pos < owner->len;
            owns input_cursor(owner);
            mutable owner->pos;
            ensures result == old(owner->data[owner->pos]);
            ensures owner->pos == old(owner->pos) + 1;
            ensures owner->len == old(owner->len);
            ensures owner->data == old(owner->data);
        } by {
            unfold(input_cursor(owner));
            observe(readable_input(owner->data, owner->len));
            execute();
            have 0 <= owner->pos by simp;
            have owner->pos <= owner->len by simp;
            have separate(
                memory(owner[0..4]),
                memory(owner->data[0..owner->len])
            ) by {
                simp();
            }
            fold(input_cursor(owner));
            frame();
            simp();
        }

    "#;

    let sources = [
        ("input_cursor_peek.c", c_source),
        ("input_cursor_take.c", take_c_source),
    ];
    let final_simp = click_source
        .rfind("simp();")
        .expect("final simp should exist");
    let position = expansion::position_at_offset(click_source, final_simp);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("the grouped simp should emit a non-circular surface certificate");
    verify_c0_sources(&expanded, &sources)
        .expect("the grouped simp surface certificate should replay from fresh source");
}

#[test]
fn explicit_store_step_with_unfolded_resource_facts_verifies() {
    let c_source = r#"
        struct owned_string {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 owned_string_set(
            struct owned_string* owner,
            int32 index,
            int32 value
        ) {
            owner->data[index] = value;
            return value;
        }
    "#;
    let click_source = r#"
        predicate terminated_at(data: int32[], length: int32) {
            data[length] == 0
        }

        resource owned_string(owner: struct owned_string*) {
            owns owner->len;
            owns owner->cap;
            owns owner->data;
            owns owner->data[0..owner->cap];
            fact 0 <= owner->len;
            fact owner->len < owner->cap;
            fact terminated_at(owner->data, owner->len);
            fact separate(
                memory(owner[0..4]),
                memory(owner->data[0..owner->cap])
            );
        }

        verifying "owned_string_set.c";

        int32 owned_string_set(
            struct owned_string* owner,
            int32 index,
            int32 value
        ) {
            requires 0 <= index;
            requires index < owner->len;
            owns owned_string(owner);
            ensures result == value;
            ensures owner->data[index] == value;
        } by {
            unfold(owned_string(owner));
            unfold(terminated_at);
            step() using {
                0 <= index;
                index < owner->len;
                loadable(owner->len);
                loadable(owner->cap);
                loadable(owner->data);
                0 <= owner->len;
                owner->len < owner->cap;
                terminated_at(owner->data, owner->len);
                separate(
                    memory(owner[0..4]),
                    memory(owner->data[0..owner->cap])
                );
                owner->data[owner->len] == 0;
            }
            have terminated_at(owner->data, owner->len) by {
                unfold(terminated_at);
                simp();
            }
            have owner->data[owner->len] == 0 by simp;
            have 0 <= owner->len by simp;
            have owner->len < owner->cap by simp;
            have separate(
                memory(owner[0..4]),
                memory(owner->data[0..owner->cap])
            ) by {
                simp();
            }
            fold(owned_string(owner));
            step();
            simp();
        }
    "#;

    verify_c0_sources(click_source, &[("owned_string_set.c", c_source)])
        .expect("explicit store certificate should verify");
}

#[test]
fn expanded_read_step_keeps_named_range_separation_premises() {
    let c_source = r#"
        struct owned_string {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 owned_string_pop(struct owned_string* owner) {
            int32 index;
            int32 value;
            index = owner->len - 1;
            value = owner->data[index];
            owner->data[index] = 0;
            owner->len = index;
            return value;
        }
    "#;
    let click_source = r#"
        predicate terminated_at(data: int32[], length: int32) {
            data[length] == 0
        }

        resource owned_string(owner: struct owned_string*) {
            owns owner->len;
            owns owner->cap;
            owns owner->data;
            owns owner->data[0..owner->cap];
            fact 0 <= owner->len;
            fact owner->len < owner->cap;
            fact terminated_at(owner->data, owner->len);
            fact separate(
                memory(owner[0..4]),
                memory(owner->data[0..owner->cap])
            );
        }

        verifying "owned_string_pop.c";

        int32 owned_string_pop(struct owned_string* owner) {
            requires 1 <= owner->len;
            owns owned_string(owner);
            mutable owner[0..1], (owner->data + (owner->len - 1))[0..1];
            ensures result == old(owner->data[owner->len - 1]);
            ensures owner->len == old(owner->len) - 1;
            ensures owner->cap == old(owner->cap);
            ensures owner->data == old(owner->data);
            ensures owner->data[owner->len] == 0;
        } by {
            unfold(owned_string(owner));
            have 0 <= owner->len - 1 by simp;
            have owner->len - 1 < owner->len by simp;
            execute();
            have terminated_at(owner->data, owner->len) by {
                unfold(terminated_at);
                simp();
            }
            have 0 <= owner->len by simp;
            have owner->len < owner->cap by simp;
            have separate(
                memory(owner[0..4]),
                memory(owner->data[0..owner->cap])
            ) by {
                simp();
            }
            fold(owned_string(owner));
            frame();
            simp();
        }
    "#;
    let execute_offset = click_source
        .find("execute()")
        .expect("proof should contain execute_rest");
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
        &[("owned_string_pop.c", c_source)],
        line,
        column,
    )
    .expect("the read step's generated surface certificate should replay");

    let strict_limits = crate::instrumentation::TacticLimits {
        simple: std::time::Duration::from_secs(30),
        smart: std::time::Duration::from_millis(100),
        control: std::time::Duration::from_secs(30),
    };
    let deadline_error = crate::instrumentation::with_tactic_limits(strict_limits, || {
        verify_c0_sources(&expanded, &[("owned_string_pop.c", c_source)])
    })
    .expect_err("an over-budget deferred tactic should stop verification directly");
    assert!(
        deadline_error.message().contains("time limit exceeded"),
        "unexpected deferred-tactic failure: {}",
        deadline_error.message()
    );

    let generous_limits = crate::instrumentation::TacticLimits {
        simple: std::time::Duration::from_secs(30),
        smart: std::time::Duration::from_secs(30),
        control: std::time::Duration::from_secs(30),
    };
    crate::instrumentation::with_tactic_limits(generous_limits, || {
        verify_c0_sources(&expanded, &[("owned_string_pop.c", c_source)])
    })
    .expect("the expanded read certificate should verify as a complete proof");
}

#[test]
fn location_verification_skips_unrelated_function_proofs() {
    let good_c = r#"
int32 good(int32 x) {
    return x;
}
"#;
    let bad_c = r#"
int32 bad(int32 x) {
    return x;
}
"#;
    let click_source = r#"
verifying "good.c";
verifying "bad.c";

int32 good(int32 x) {
    ensures result == x;
} by {
    execute();
    simp();
}

int32 bad(int32 x) {
    ensures result == x + 1;
} by {
    execute();
    simp();
}
"#;
    let sources = [("good.c", good_c), ("bad.c", bad_c)];
    let selected = click_source.find("ensures result == x;").unwrap();
    let position = expansion::position_at_offset(click_source, selected);

    verify_c0_sources(click_source, &sources)
        .expect_err("complete verification should reject the bad function");
    let verified = verify_c0_sources_at(click_source, &sources, position.line, position.column)
        .expect("location verification should skip the unrelated bad proof");
    assert!(
        verified
            .iter()
            .all(|theorem| theorem.function_block.signature().name() == "good")
    );
}

#[test]
fn location_verification_checks_called_function_dependencies() {
    let callee_c = r#"
int32 callee(int32 x) {
    return x;
}
"#;
    let caller_c = r#"
int32 caller(int32 x) {
    int32 result;
    result = callee(x);
    return result;
}
"#;
    let click_source = r#"
verifying "callee.c";
verifying "caller.c";

int32 callee(int32 x) {
    ensures result == x + 1;
} by {
    execute();
    simp();
}

int32 caller(int32 x) {
    ensures result == x + 1;
} by {
    execute();
    simp();
}
"#;
    let sources = [("callee.c", callee_c), ("caller.c", caller_c)];
    let caller_proof = click_source.rfind("execute()").unwrap();
    let position = expansion::position_at_offset(click_source, caller_proof);

    let error = verify_c0_sources_at(click_source, &sources, position.line, position.column)
        .expect_err("targeted caller verification must check its callee dependency");
    assert!(error.message().contains("callee"), "{}", error.message());
}

#[test]
fn modular_call_snapshot_anchor_replays_with_owned_resource() {
    let init_c = r#"
struct box {
    int32 value;
    int32* data;
};

int32 box_init(struct box* owner, int32 data[], int32 value) {
    owner->value = 0;
    owner->data = data;
    data[0] = 0;
    return 0;
}
"#;
    let read_c = r#"
struct box {
    int32 value;
    int32* data;
};

int32 box_read(struct box* owner) {
    return owner->data[0];
}
"#;
    let set_c = r#"
struct box {
    int32 value;
    int32* data;
};

int32 box_set(struct box* owner, int32 value) {
    int32 index;
    index = owner->value;
    owner->data[index] = value;
    owner->value = index + 1;
    return owner->value;
}
"#;
    let pipeline_c = r#"
struct box {
    int32 value;
    int32* data;
};

int32 box_pipeline(struct box* owner, int32 data[], int32 value) {
    int32 ignored;
    int32 observed;
    ignored = box_init(owner, data, value);
    ignored = box_set(owner, value);
    observed = box_read(owner);
    return observed;
}
"#;
    let click_source = r#"
resource owned_box(owner: struct box*) {
    owns owner->value;
    owns owner->data;
    owns owner->data[0..1];
    fact separate(memory(object(owner)), memory(owner->data[0..1]));
}

verifying "box_init.c";
verifying "box_set.c";
verifying "box_read.c";
verifying "box_pipeline.c";

int32 box_init(struct box* owner, int32 data[], int32 value) {
    requires separate(memory(object(owner)), memory(data[0..1]));
    consumes object(owner);
    consumes data[0..1];
    mutable object(owner), data[0..1];
    produces owned_box(owner);
    ensures owner->data == data;
    ensures owner->value == 0;
} by {
    execute();
    have separate(memory(object(owner)), memory(owner->data[0..1])) by simp;
    fold(owned_box(owner));
    frame();
    simp();
}

int32 box_read(struct box* owner) {
    views owned_box(owner);
    immutable;
    ensures result == owner->data[0] by auto;
}

int32 box_set(struct box* owner, int32 value) {
    requires owner->value == 0;
    owns owned_box(owner);
    mutable owner->value, (owner->data + owner->value)[0..1];
    ensures result == old(owner->value) + 1;
    ensures owner->value == old(owner->value) + 1;
    ensures owner->data[old(owner->value)] == value;
} by {
    unfold(owned_box(owner));
    have owner->value < 2147483647 by simp;
    execute();
    have separate(memory(object(owner)), memory(owner->data[0..1])) by simp;
    fold(owned_box(owner));
    frame();
    simp();
}

int32 box_pipeline(struct box* owner, int32 data[], int32 value) {
    requires separate(memory(object(owner)), memory(data[0..1]));
    consumes object(owner);
    consumes data[0..1];
    produces owned_box(owner);
    ensures result == value;
} by {
    execute_until(statement(3));
    have owner->data == data by simp;
    have owner->value == 0 by simp;
    step() using {
        owner->value == 0;
        loadable(old(object(owner)));
        loadable(old(data[0..1]));
    }
    have owner->data[at(statement(3).entry, owner->value)] == value by {
        assumption();
    }
    have owner->data[0] == value by simp;
    step() using {
        owner->data[0] == value;
        loadable(old(object(owner)));
        loadable(old(data[0..1]));
    }
    execute();
    simp();
}
"#;

    verify_c0_sources(
        click_source,
        &[
            ("box_init.c", init_c),
            ("box_set.c", set_c),
            ("box_read.c", read_c),
            ("box_pipeline.c", pipeline_c),
        ],
    )
    .expect("an explicit call-entry snapshot should replay with an owned resource");
}

#[test]
fn execute_until_expands_mixed_snapshot_call_postconditions() {
    let zero_c = r#"
struct counter {
    int32 value;
};

int32 zero(struct counter* owner) {
    owner->value = 0;
    return owner->value;
}
"#;
    let increment_c = r#"
struct counter {
    int32 value;
};

int32 increment(struct counter* owner) {
    int32 before;
    before = owner->value;
    owner->value = before + 1;
    return owner->value;
}
"#;
    let pipeline_c = r#"
struct counter {
    int32 value;
};

int32 pipeline(struct counter* owner) {
    int32 ignored;
    ignored = zero(owner);
    ignored = increment(owner);
    return owner->value;
}
"#;
    let click_source = r#"
resource counter(owner: struct counter*) {
    owns owner->value;
}

verifying "zero.c";
verifying "increment.c";
verifying "pipeline.c";

int32 zero(struct counter* owner) {
    consumes object(owner);
    mutable object(owner);
    produces counter(owner);
    ensures result == 0;
    ensures owner->value == 0;
} by {
    execute();
    fold(counter(owner));
    frame();
    simp();
}

int32 increment(struct counter* owner) {
    requires owner->value < 2147483647;
    owns counter(owner);
    mutable owner->value;
    ensures result == old(owner->value) + 1;
    ensures owner->value == old(owner->value) + 1;
} by {
    unfold(counter(owner));
    execute();
    fold(counter(owner));
    frame();
    simp();
}

int32 pipeline(struct counter* owner) {
    consumes object(owner);
    mutable object(owner);
    produces counter(owner);
    ensures result == 1;
    ensures owner->value == 1;
} by {
    execute_until(statement(3));
    have owner->value == 1 by simp;
    step() using {
        owner->value == 1;
    }
    frame();
    simp();
}
"#;
    let sources = [
        ("zero.c", zero_c),
        ("increment.c", increment_c),
        ("pipeline.c", pipeline_c),
    ];

    verify_c0_sources(click_source, &sources).expect("the original smart proof should verify");

    let frontier_have = click_source.find("have owner->value == 1 by simp").unwrap();
    let have_position = expansion::position_at_offset(click_source, frontier_have);
    let have_expanded = expand_c0_tactic_source_at(
        click_source,
        &sources,
        have_position.line,
        have_position.column,
    )
    .expect("the mixed-snapshot frontier-local fact should expand");
    assert!(!have_expanded.contains("have owner->value == 1 by simp"));
    assert!(
        have_expanded.contains("at(statement("),
        "the explicit certificate should retain a source statement anchor"
    );
    verify_c0_sources(&have_expanded, &sources)
        .expect("the mixed-snapshot frontier-local expansion should replay");

    let selected = click_source.find("execute_until").unwrap();
    let position = expansion::position_at_offset(click_source, selected);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("mixed-snapshot smart execution should expand");
    assert!(!expanded.contains("execute_until(statement(3));"));
    verify_c0_sources(&expanded, &sources)
        .expect("the mixed-snapshot smart execution expansion should replay");
}

#[test]
fn execute_until_expands_vector_storage_call_postconditions() {
    let init_c = r#"
struct buffer {
    int32 len;
    int32 cap;
    int32* data;
};

int32 buffer_init(struct buffer* owner, int32 data[], int32 capacity) {
    owner->len = 0;
    owner->cap = capacity;
    owner->data = data;
    return owner->len;
}
"#;
    let push_c = r#"
struct buffer {
    int32 len;
    int32 cap;
    int32* data;
};

int32 buffer_push(struct buffer* owner, int32 value) {
    int32 index;
    int32* data;
    index = owner->len;
    data = owner->data;
    data[index] = value;
    owner->len = index + 1;
    return owner->len;
}
"#;
    let pipeline_c = r#"
struct buffer {
    int32 len;
    int32 cap;
    int32* data;
};

int32 buffer_pipeline(
    struct buffer* owner,
    int32 data[],
    int32 capacity,
    int32 value
) {
    int32 result;
    result = buffer_init(owner, data, capacity);
    result = buffer_push(owner, value);
    return result;
}
"#;
    let click_source = r#"
resource empty_buffer(owner: struct buffer*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact owner->len == 0;
    fact 1 <= owner->cap;
    fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
}

resource buffer_storage(owner: struct buffer*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact loadable(owner->data[0..owner->len]);
    fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
}

resource nonempty_buffer(owner: struct buffer*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 1 <= owner->len;
    fact owner->len <= owner->cap;
    fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
}

verifying "buffer_init.c";
verifying "buffer_push.c";
verifying "buffer_pipeline.c";

int32 buffer_init(struct buffer* owner, int32 data[], int32 capacity) {
    requires 1 <= capacity;
    consumes object(owner);
    consumes data[0..capacity];
    mutable owner->len, owner->cap, owner->data;
    produces empty_buffer(owner);
    ensures result == 0;
    ensures owner->len == 0;
    ensures owner->cap == capacity;
    ensures owner->data == data;
} by {
    execute();
    fold(empty_buffer(owner));
    frame();
    simp();
}

int32 buffer_push(struct buffer* owner, int32 value) {
    requires owner->len < owner->cap;
    owns buffer_storage(owner);
    mutable owner->len, owner->data[owner->len..owner->len + 1];
    ensures result == old(owner->len) + 1;
    ensures owner->len == old(owner->len) + 1;
    ensures owner->data[old(owner->len)] == value;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
} by {
    unfold(buffer_storage(owner));
    execute();
    fold(buffer_storage(owner));
    frame();
    simp();
}

int32 buffer_pipeline(
    struct buffer* owner,
    int32 data[],
    int32 capacity,
    int32 value
) {
    requires 1 <= capacity;
    consumes object(owner);
    consumes data[0..capacity];
    produces nonempty_buffer(owner) by {
        execute_until(statement(2));
        unfold(empty_buffer(owner));
        have 0 <= owner->len by simp;
        have owner->len <= owner->cap by simp;
        have loadable(owner->data[0..owner->len]) by simp;
        fold(buffer_storage(owner));
        execute_until(statement(3));
        unfold(buffer_storage(owner));
        have owner->len == 1 by simp;
        have 1 <= owner->len by simp;
        fold(nonempty_buffer(owner));
        step() using {};
    }
}
"#;
    let sources = [
        ("buffer_init.c", init_c),
        ("buffer_push.c", push_c),
        ("buffer_pipeline.c", pipeline_c),
    ];

    verify_c0_sources(click_source, &sources)
        .expect("the original vector-shaped proof should verify");

    let selected = click_source.rfind("execute_until").unwrap();
    let position = expansion::position_at_offset(click_source, selected);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("vector-shaped mixed-snapshot smart execution should expand");
    assert!(!expanded.contains("execute_until(statement(3));"));
    verify_c0_sources(&expanded, &sources)
        .expect("the vector-shaped mixed-snapshot expansion should replay");
}

#[test]
fn tactic_expansion_includes_a_call_at_the_execute_until_endpoint() {
    let callee_c = r#"
int32 callee(int32 x) {
    return x;
}
"#;
    let caller_c = r#"
int32 caller(int32 x) {
    int32 result;
    result = callee(x);
    return result;
}
"#;
    let click_source = r#"
verifying "callee.c";
verifying "caller.c";

int32 callee(int32 x) {
    ensures result == x;
} by {
    execute();
    simp();
}

int32 caller(int32 x) {
    ensures result == x;
} by {
    execute_until(statement(1));
    execute();
    simp();
}
"#;
    let sources = [("callee.c", callee_c), ("caller.c", caller_c)];
    let selected = click_source.find("execute_until").unwrap();
    let position = expansion::position_at_offset(click_source, selected);

    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("the endpoint call dependency should be verified before expansion");
    assert!(!expanded.contains("execute_until(statement(1));"));
}

#[test]
fn verification_session_reuses_certified_dependencies_and_rechecks_target() {
    let callee_c = r#"
int32 callee(int32 x) {
    return x;
}
"#;
    let caller_c = r#"
int32 caller(int32 x) {
    int32 result;
    result = callee(x);
    return result;
}
"#;
    let click_source = r#"
verifying "callee.c";
verifying "caller.c";

int32 callee(int32 x) {
    ensures result == x;
} by {
    execute();
    simp();
}

int32 caller(int32 x) {
    ensures result == x;
} by {
    execute();
    simp();
}
"#;
    let sources = [("callee.c", callee_c), ("caller.c", caller_c)];
    let (session, _) =
        C0VerificationSession::new(click_source, &sources).expect("baseline should verify");
    let caller_simp = click_source.rfind("simp();").unwrap();
    let position = expansion::position_at_offset(click_source, caller_simp);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("caller simp should expand");
    let expanded_position =
        c0_tactic_source_position(&expanded, &sources, "caller.contract", 0).unwrap();

    let verified = session
        .verify_at(&expanded, expanded_position.line, expanded_position.column)
        .expect("session should verify the rewritten caller");
    assert!(
        verified
            .iter()
            .all(|theorem| theorem.function_block.signature().name() == "caller")
    );

    let broken_target = expanded.replacen("assumption();", "left();", 1);
    session
        .verify_at(
            &broken_target,
            expanded_position.line,
            expanded_position.column,
        )
        .expect_err("the selected function must be rechecked");

    let changed_dependency = expanded.replacen(
        "int32 callee(int32 x) {\n    ensures result == x;",
        "int32 callee(int32 x) {\n    ensures result == x + 1;",
        1,
    );
    let error = session
        .verify_at(
            &changed_dependency,
            expanded_position.line,
            expanded_position.column,
        )
        .expect_err("dependency source changes must invalidate the baseline session");
    assert!(
        error.message().contains("outside the selected proof unit"),
        "{}",
        error.message()
    );

    let shifted = expanded.replacen("int32 caller", "\n\nint32 caller", 1);
    let shifted_position =
        c0_tactic_source_position(&shifted, &sources, "caller.contract", 0).unwrap();
    assert_ne!(shifted_position.line, position.line);
    session
        .verify_at(&shifted, shifted_position.line, shifted_position.column)
        .expect("session selection should follow the rewritten claim, not baseline coordinates");
}

#[test]
fn verification_session_keeps_partial_and_termination_rules_separate() {
    let good_c = r#"int32 countdown(int32 n) {
    int32 result;
    if (n > 0) {
        result = countdown(n - 1);
        return result;
    }
    return 0;
}"#;
    let partial_c = r#"int32 stuck(int32 n) {
    int32 result;
    if (n > 0) {
        result = stuck(n);
        return result;
    }
    return 0;
}"#;
    let click_source = r#"verifying "countdown.c";
verifying "stuck.c";

int32 countdown(int32 n) {
    decreases n;
    ensures result == 0 by auto;
}

int32 stuck(int32 n) {
    ensures result == 0 by auto;
}"#;
    let sources = [("countdown.c", good_c), ("stuck.c", partial_c)];
    let (session, _) =
        C0VerificationSession::new(click_source, &sources).expect("both contracts should verify");

    assert!(session.function_termination_is_verified("countdown"));
    assert!(!session.function_termination_is_verified("stuck"));
}

/// `condition_polarity_equivalent` used to answer through
/// `canonical_order_condition(left) == canonical_order_condition(right)`.
/// Only comparisons have a canonical order form, so every pair of
/// non-comparison conditions compared equal through `None == None`, and any
/// such premise counted as available once the context held any other
/// non-comparison condition.
#[test]
fn unrelated_non_comparison_conditions_are_not_polarity_equivalent() {
    let overflow = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedAddOverflows(
            Box::new(Bitvector32Term::Variable(Variable(1))),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        false,
    );
    let constant = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let equality = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(Variable(2))),
            Box::new(Bitvector32Term::Constant(7)),
        ),
        true,
    );

    for (left, right) in [
        (&overflow, &constant),
        (&constant, &equality),
        (&overflow, &equality),
    ] {
        assert!(
            !condition_polarity_equivalent(left, right),
            "conditions without a canonical order form must not match each other:\n  {left:?}\n  {right:?}"
        );
    }

    // Each is still equivalent to itself, and the canonical order form still
    // relates the two spellings of one comparison.
    for condition in [&overflow, &constant, &equality] {
        assert!(condition_polarity_equivalent(condition, condition));
    }
    let less_than = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessThan(
            Box::new(Bitvector32Term::Variable(Variable(1))),
            Box::new(Bitvector32Term::Variable(Variable(2))),
        ),
        true,
    );
    let greater_equal = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterEqual(
            Box::new(Bitvector32Term::Variable(Variable(2))),
            Box::new(Bitvector32Term::Variable(Variable(1))),
        ),
        false,
    );
    assert!(condition_polarity_equivalent(&less_than, &greater_equal));
}

#[test]
fn unfolding_composite_rejects_concretely_overlapping_owned_children() {
    let c_source = r#"
        int32 preserve(int32* data) {
            return 0;
        }
    "#;
    let click_source = r#"
        resource overlapping(data: int32*) {
            owns data[0..2];
            owns data[1..3];
            fact separate(memory(data[0..2]), memory(data[1..3]));
        }

        verifying "preserve.c";

        int32 preserve(int32* data) {
            owns overlapping(data);
            ensures result == 0;
        } by {
            unfold(overlapping(data));
            execute();
            simp();
        }
    "#;

    let error = verify_c0_sources(click_source, &[("preserve.c", c_source)])
        .expect_err("a composite fact must not authorize overlapping owned children");
    assert!(
        error
            .message()
            .contains("overlapping owned memory resource facts"),
        "{}",
        error.message()
    );
}

#[test]
fn unfolding_composite_accepts_propositionally_equal_arguments() {
    let c_source = r#"
        int32 preserve(int32* left, int32* right) {
            return 0;
        }
    "#;
    let click_source = r#"
        resource cell(data: int32*) {
            owns data[0..1];
        }

        verifying "preserve.c";

        int32 preserve(int32* left, int32* right) {
            requires left == right;
            owns cell(left);
            ensures result == 0;
        } by {
            unfold(cell(right));
            execute();
            fold(cell(left));
            simp();
        }
    "#;

    verify_c0_sources(click_source, &[("preserve.c", c_source)])
        .expect("unfold should retain its equality-aware resource-consumption fallback");
}

#[test]
fn incremental_selection_follows_reverse_call_dependencies_and_ignores_comments() {
    let sources = [
        ("leaf.c", "int32 leaf(int32 x) { return x; }"),
        (
            "middle.c",
            "int32 middle(int32 x) { int32 y = leaf(x); return y; }",
        ),
        (
            "top.c",
            "int32 top(int32 x) { int32 y = middle(x); return y; }",
        ),
        ("unrelated.c", "int32 unrelated(int32 x) { return x; }"),
    ];
    let baseline = r#"
verifying "leaf.c";
verifying "middle.c";
verifying "top.c";
verifying "unrelated.c";
int32 leaf(int32 x) { ensures result == x; } by simp;
int32 middle(int32 x) { ensures result == x; } by auto;
int32 top(int32 x) { ensures result == x; } by auto;
int32 unrelated(int32 x) { ensures result == x; } by auto;
"#;
    let changed = baseline.replacen("} by simp;", "} by auto;", 1);
    let selection = c0_incremental_selection(&changed, &sources, baseline, &sources).unwrap();
    assert_eq!(selection.selected_functions, ["leaf", "middle", "top"]);
    assert_eq!(selection.reused_functions, ["unrelated"]);
    assert!(!selection.full_rebuild);
    let incremental =
        verify_c0_sources_functions(&changed, &sources, selection.selected_functions.clone());
    let clean = verify_c0_sources(&changed, &sources);
    assert!(clean.is_ok(), "clean verification failed: {clean:?}");
    assert_eq!(incremental.is_ok(), clean.is_ok(), "{incremental:?}");

    let commented_sources = [
        (
            "leaf.c",
            "// formatting-only edit\nint32 leaf(int32 x) { return x; }",
        ),
        sources[1],
        sources[2],
        sources[3],
    ];
    let unchanged =
        c0_incremental_selection(baseline, &commented_sources, baseline, &sources).unwrap();
    assert!(unchanged.selected_functions.is_empty(), "{unchanged:?}");
    assert_eq!(unchanged.reused_functions.len(), 4);
}

#[test]
fn incremental_selection_rebuilds_all_functions_for_shared_logic_changes() {
    let sources = [
        ("first.c", "int32 first(int32 x) { return x; }"),
        ("second.c", "int32 second(int32 x) { return x; }"),
    ];
    let baseline = r#"
verifying "first.c";
verifying "second.c";
predicate allowed(x: int32) { x == x }
int32 first(int32 x) { ensures result == x; } by simp;
int32 second(int32 x) { ensures result == x; } by simp;
"#;
    let changed = baseline.replace("x == x", "x == 0");
    let selection = c0_incremental_selection(&changed, &sources, baseline, &sources).unwrap();
    assert!(selection.full_rebuild);
    assert_eq!(selection.selected_functions, ["first", "second"]);
    assert!(selection.reused_functions.is_empty());
}
