use super::*;

/// The uint64 bridge creates nested `have` proofs. A missing listed premise
/// must return the arithmetic goal's diagnostic, not panic while wrapping
/// the nested bridge's already-rendered diagnostic inside a new summary.
#[test]
fn wide_arithmetic_unavailable_premise_returns_one_diagnostic() {
    let source = "theorem bound(x: uint64) { requires x <= 100u64; ensures x <= 1000u64 by { arithmetic() using { x <= 50u64; } } }";
    let error = verify_click_theorems(source).expect_err("an unavailable premise must be refused");
    assert!(
        error.raw_summary().contains("unavailable exact premise"),
        "{error:?}"
    );
    assert!(!error.raw_summary().contains("\n  stage:"));
    assert!(!error.raw_summary().contains("\n  goal:"));
    assert_eq!(
        error.message().matches("\n  stage:").count(),
        1,
        "{error:?}"
    );
    assert!(error.message().contains("goal: x <= 1000u64"), "{error:?}");
}

/// A tiny budget stops the wide arithmetic tactic before its bridge can
/// finish lowering. Report one bounded diagnostic rather than panicking while
/// wrapping the nested refusal.
#[test]
fn wide_arithmetic_budget_refusal_does_not_panic() {
    let source = "theorem bound(x: uint64) { requires x <= 100u64; ensures x + 1u64 + 1u64 <= 1000u64 by { arithmetic() using { x <= 100u64; } } }";
    let error = crate::instrumentation::with_tactic_work_limits(
        crate::instrumentation::TacticWorkLimits {
            simple: 1,
            smart: 1,
            control: 1,
        },
        || verify_click_theorems(source),
    )
    .expect_err("the constrained bridge must refuse locally");
    assert!(error.raw_summary().contains("budget"), "{error:?}");
    assert!(!error.raw_summary().contains("\n  stage:"));
    assert_eq!(
        error.message().matches("\n  stage:").count(),
        1,
        "{error:?}"
    );
}

#[test]
fn uninitialized_mutex_is_a_named_proof_prerequisite() {
    let c_source = r#"
        #include <pthread.h>
        struct cell { pthread_mutex_t mu; };
        void use_mutex(struct cell *cell) { pthread_mutex_lock(&cell->mu); }
    "#;
    let click_source = r#"
        target "x86_64-linux-userspace";
        runtime "modeled-pthread";
        verifying "mutex.c";
        void use_mutex(struct cell *cell) { ensures 0 == 0; } by { step(); }
    "#;
    let error = verify_c0_sources(click_source, &[("mutex.c", c_source)]).unwrap_err();
    assert_eq!(error.kind(), ClickErrorKind::Proof, "{}", error.message());
    assert!(
        error
            .message()
            .contains("could not prove that mutex `cell` was initialized on this path"),
        "{error:?}"
    );
    assert_eq!(
        error.concise_report_parts().0,
        "proof error in `use_mutex`:\n  could not prove that mutex `cell` was initialized on this path"
    );
    assert!(!error.message().contains("runtime error"), "{error:?}");
}

#[test]
fn worker_without_protocol_contract_is_a_proof_error() {
    let c_source = r#"
        #include <pthread.h>
        #include <stddef.h>
        struct box { pthread_mutex_t mu; int value; };
        void *idle(void *arg) { return 0; }
        void start(struct box *box) {
            pthread_t handle;
            int status;
            pthread_mutex_init(&box->mu, 0);
            status = pthread_create(&handle, NULL, idle, box);
        }
    "#;
    let click_source = r#"
        target "x86_64-linux-userspace";
        runtime "modeled-pthread";
        resource box_state(box: struct box*) {
            field value: int32;
            owns box->value;
            fact box->value == value;
        }
        verifying "mutex.c";
        void *idle(void *arg) { ensures result == 0; } by { execute(); simp(); }
        void start(struct box *box) {
            owns box->mu;
            requires aligned(&box->mu, 8);
            owns state: box_state(box);
            ensures 0 == 0;
        } by {
            step();
            step();
            let { lifetime: mutex_lifetime } = step(pthread_mutex_init(&box->mu, 0), { state: state });
            step();
        }
    "#;
    let error = verify_c0_sources(click_source, &[("mutex.c", c_source)]).unwrap_err();
    assert_eq!(error.kind(), ClickErrorKind::Proof, "{}", error.message());
    assert!(
        error
            .message()
            .contains("calls with live mutex protocols require contract protocol effects"),
        "{error:?}"
    );
    assert!(!error.message().contains("runtime error"), "{error:?}");
}

#[test]
fn concise_error_context_preserves_click_binder_colons() {
    assert_eq!(
        concise_error_segments("foo: exists (path: Path) { x: y }: qux"),
        ["foo", "exists (path: Path) { x: y }", "qux"]
    );
    assert_eq!(
        concise_error_segments("foo: `witness { path: value }`: bar"),
        ["foo", "`witness { path: value }`", "bar"]
    );
    assert_eq!(
        concise_error_segments("can't close: current goal is exists (path: Path)"),
        ["can't close", "current goal is exists (path: Path)"]
    );
}

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
#[ignore = "nightly: 4s in the parallel gate"]
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
            fact owner->cap <= 1073741823;
            fact viewable(owner->data[0..owner->len]);
            fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
        }

        resource allocated(owner: struct vector*) {
            owns owner->len;
            owns owner->cap;
            owns owner->data;
            owns allocation(owner->data, owner->cap * 4);
            owns owner->data[0..owner->cap];
            fact 0 <= owner->len;
            fact owner->len <= owner->cap;
            fact 1 <= owner->cap;
            fact owner->cap <= 1073741823;
            fact viewable(owner->data[0..owner->len]);
            fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
        }

        verifying "push.c";
        verifying "caller.c";

        int32 push(struct vector* owner, int32 value) {
            requires owner->len < owner->cap;
            owns storage(owner);
            ensures result == old(owner->len) + 1;
            ensures owner->len == old(owner->len) + 1;
            ensures 1 <= owner->len;
            ensures owner->cap == old(owner->cap);
            ensures owner->data == old(owner->data);
        } by {
            unfold(storage(owner));
            execute();
            fold(storage(owner));
            simp();
        }

        int32 caller(struct vector* owner, int32 value) {
            requires owner->len < owner->cap;
            consumes allocated(owner);
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
            simp();
        }
    "#;

    let sources = [("push.c", push_c), ("caller.c", caller_c)];
    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("a storage-only callee should preserve its caller's allocation authority");
    assert!(events.iter().all(|event| !matches!(
        event,
        crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
            if matches!(
                name.as_str(),
                "whole-claim certificate construction"
                    | "whole-claim certificate validation"
                    | "whole-contract certificate construction"
                    | "whole-contract certificate validation"
            )
    )));

    let push_start = click_source.find("int32 push").unwrap();
    let simp_offset = push_start + click_source[push_start..].find("simp();").unwrap();
    let position = expansion::position_at_offset(click_source, simp_offset);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("push postconditions should expand explicitly");
    assert!(
        expanded.contains("apply(int32_increment_preserves_order("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &sources).expect("expanded push proof should check");
}

/// Every external pointer parameter shares one block, so a store to
/// `visited[cur]` can also be spelled through `next`, with the difference of
/// the two bases folded into the index. When the index has no source name —
/// `cur` has since been reassigned, so its store-time value is a term only the
/// lowering names — both spellings read `name[…]`, and the shorter text used
/// to win: a `simp` refusal about `visited[k]` named "the store to `next[…]`".
/// The address belongs to the base its bare index is taken from.
#[test]
fn an_unnamed_store_index_is_spelled_through_its_own_base() {
    let base = |variable: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(variable))),
            byte_width: 4,
        },
    };
    let parameters = vec![
        syntax::C0Parameter::new(C0Type::Int32Pointer, "next".to_string(), None),
        syntax::C0Parameter::new(C0Type::Int32Pointer, "visited".to_string(), None),
    ];
    let arguments = vec![
        CExpression::Value(CValue::typed_pointer(base(100_000), CType::Int32Pointer)),
        CExpression::Value(CValue::typed_pointer(base(100_001), CType::Int32Pointer)),
    ];
    // `visited + old_cur * 4`, with `old_cur` a variable no local names.
    let store = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Add(
            Box::new(base(100_001).offset),
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(Variable(1_000_000))),
                byte_width: 4,
            }),
        ),
    };
    assert_eq!(
        super::diagnostics::source_cell_text_for_tests(
            &store,
            ParameterBinding::new(&parameters, &arguments)
        )
        .as_deref(),
        Some("visited[…]")
    );
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
        super::checking::pointer_element_index_from_base(&field, &base, &PureFactContext::new())
    });

    assert_eq!(index, Some(Bitvector32Term::Constant(1)));
}

#[test]
fn verifier_diagnostics_are_bounded_deterministically_at_utf8_boundaries() {
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
}

#[test]
fn execution_effect_diagnostics_omit_raw_memory_snapshots() {
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(8),
    };
    let before = CMemory::new().store(pointer.clone(), int32(1));
    let after = before.clone().store(pointer.clone(), int32(2));
    let facts = vec![
        ExecutionPureFact::new(Proposition::CMemoryMutatesOnly {
            before: before.clone(),
            after: after.clone(),
            writes: vec![(pointer.clone(), 4)],
        }),
        ExecutionPureFact::new(Proposition::CMemoryEffectSummary {
            before: before.clone(),
            after: after.clone(),
            mutable_ranges: vec![CMemoryRange::new(
                pointer.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )],
        }),
        ExecutionPureFact::new(Proposition::CHeapAllocationFreed {
            before,
            after,
            allocation_base: pointer,
            bytes: Bitvector32Term::Constant(4),
        }),
    ];

    let description = super::diagnostics::describe_execution_pure_facts(&facts);

    assert!(description.contains("changed between"), "{description}");
    assert!(
        description.contains("written range(s) between"),
        "{description}"
    );
    assert!(description.contains("freed between"), "{description}");
    assert!(!description.contains("CMemory"), "{description}");
    assert!(
        !description.contains("diagnostic truncated"),
        "{description}"
    );
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
                        crate::kernel::LoadKind::Bits32,
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
    let limits = crate::instrumentation::TacticWorkLimits {
        simple: 1_000_000,
        smart: 0,
        control: 1_000_000,
    };
    let tactic = crate::instrumentation::TacticEvent {
        source_tactic_path: None,
        claim: "wide-condition.contract".to_string(),
        tactic_index: 0,
        tactic_name: "execute_until".to_string(),
        class: "smart".to_string(),
        statement_index: 0,
        source_index: 0,
    };

    let error = crate::instrumentation::with_tactic_work_limits(limits, || {
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
    // Unnamed operands retain distinct identities.
    assert!(
        error
            .message()
            .contains("target: <unnamed A> == <unnamed B>"),
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

/// A condition search that finds no derivation prints the goal it looked for
/// and the premises it searched, each with its operands in the source's names.
/// It used to read "did not derive signed less-or-equal is true from 2
/// ambient condition facts: [signed less-or-equal is true, ...]", which names
/// neither the goal nor any premise.
#[test]
fn a_condition_search_miss_spells_its_goal_and_premises() {
    let x = Bitvector32Term::Variable(Variable(1));
    let y = Bitvector32Term::Variable(Variable(2));
    let at_most = |term: &Bitvector32Term, bound: u32| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(term.clone()),
                Box::new(Bitvector32Term::Constant(bound)),
            ),
            true,
        )
    };
    let goal = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessEqual(Box::new(x.clone()), Box::new(y.clone())),
        true,
    );
    let parameters = vec![
        syntax::C0Parameter::new(C0Type::Int32, "x".to_string(), None),
        syntax::C0Parameter::new(C0Type::Int32, "y".to_string(), None),
    ];
    let arguments = vec![
        CExpression::Value(CValue::Int32(x.clone())),
        CExpression::Value(CValue::Int32(y.clone())),
    ];
    let message = super::proof::describe_condition_search_miss(
        &goal,
        &[at_most(&x, 10), at_most(&y, 10)],
        ParameterBinding::new(&parameters, &arguments),
    );
    assert!(
        message
            .contains("did not derive `x <= y` from 2 ambient condition facts: [x <= 10, y <= 10]"),
        "{message}"
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
        derivation.check(&assumptions_from_propositions(&facts)),
        "the selected certificate premises must check"
    );
}

#[test]
fn verifier_diagnostics_bound_fact_items() {
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
}

#[test]
fn expired_project_deadline_outweighs_semantic_mismatch_diagnostic() {
    let error = crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
        ClickError::new("execution proof changed more than the certified ghost regions")
    });

    assert!(
        error
            .message()
            .contains("wall-clock crash-containment bound"),
        "{error:?}"
    );
    assert!(!error.message().contains("ghost regions"), "{error:?}");
}

#[test]
fn exhausted_work_budget_outweighs_missing_path_goal_diagnostic() {
    let limits = crate::instrumentation::TacticWorkLimits {
        simple: 0,
        smart: 1,
        control: 1,
    };
    let tactic = crate::instrumentation::TacticEvent {
        source_tactic_path: None,
        claim: "copy3.contract".to_string(),
        tactic_index: 0,
        tactic_name: "close_invariants".to_string(),
        class: "simple".to_string(),
        statement_index: 0,
        source_index: 0,
    };
    let error = crate::instrumentation::with_tactic_work_limits(limits, || {
        crate::instrumentation::emit(crate::instrumentation::VerificationEvent::TacticStarted(
            tactic.clone(),
        ));
        assert!(crate::instrumentation::deadline_exceeded());
        let error = ClickError::new("invariant 1 is missing path goal: ForAll { ... }");
        crate::instrumentation::emit(crate::instrumentation::VerificationEvent::TacticFailed(
            tactic,
        ));
        error
    });

    assert!(
        error.message().contains("deterministic simple work budget"),
        "{error:?}"
    );
    assert!(!error.message().contains("missing path goal"), "{error:?}");
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
    let assumptions = PureFactContext::new().assume_proposition(proposition.clone());

    assert_eq!(
        simp_proposition(&proposition, &assumptions),
        SimpProposition::True
    );
}

#[test]
fn failed_algebraic_simp_reports_claim_without_internal_schema_dump() {
    let source = r#"
        spec enum Maybe<T> { None, Some(T) }
        theorem false_reconstruction(value: Maybe<int32>) {
            ensures match value {
                Maybe::None => Maybe<int32>::Some(0),
                Maybe::Some(x) => Maybe<int32>::Some(x),
            } == value by simp;
        }
    "#;
    let error = verify_c0_sources(source, &[]).unwrap_err();
    let message = error.message();
    assert!(
        message.contains("false_reconstruction.ensures_0"),
        "{message}"
    );
    assert!(
        message.contains("could not establish `match value {"),
        "{message}"
    );
    assert!(!message.contains("AlgebraicSchemas"), "{message}");
    assert!(!message.contains("AlgebraicTerm"), "{message}");
    assert!(message.contains("search candidates:"), "{message}");
    assert!(message.len() < 4000, "{message}");
}

/// A goal whose shape has no prepared sentence used to fall through to the
/// kernel proposition's `Debug`, which carries every variant of every
/// reachable datatype family for each occurrence of a value, and the `simp`
/// report printed the goal twice.  The bounded printer renders the same claim
/// in its source vocabulary, once.
#[test]
fn failed_compound_algebraic_simp_renders_the_goal_once_without_a_debug_dump() {
    let source = r#"
        spec enum Color { Red, Black }
        spec enum RbTree { Empty, Node(int32, Color, RbTree, RbTree) }

        function color_bit(color: Color) -> int32 {
            match color {
                Color::Red => 0,
                Color::Black => 1,
            }
        }

        function root_color(tree: RbTree) -> Color {
            match tree {
                RbTree::Empty => Color::Black,
                RbTree::Node(value, color, left, right) => color,
            }
        }

        theorem color_bit_is_two(t: RbTree) {
            ensures color_bit(root_color(t)) == 2 and root_color(t) == Color::Red by {
                simp();
            }
        }
    "#;
    let error = verify_c0_sources(source, &[]).unwrap_err();
    let message = error.message();
    assert!(message.contains("color_bit_is_two.ensures_0"), "{message}");
    assert!(message.contains("root_color("), "{message}");
    assert!(message.contains("Color::Red"), "{message}");
    assert!(
        message.contains("could not establish `color_bit(root_color(t)) == 2 and "),
        "{message}"
    );
    assert!(message.contains("search candidates:"), "{message}");
    for marker in [
        "AlgebraicSchemas",
        "AlgebraicTerm",
        "AlgebraicType",
        "AlgebraicVariantType",
        "ClickFunctionApplication",
        "algebraic_type:",
        "variants:",
        "grounded:",
        "rigid:",
    ] {
        assert!(!message.contains(marker), "{marker}: {message}");
    }
    // The goal is reported once, not once as the simplified proposition and
    // again as the missing fact.
    let focused = message.split("search candidates:").next().unwrap();
    assert_eq!(focused.matches("\n  goal:").count(), 1, "{message}");
    assert!(!message.contains("missing pure fact"), "{message}");
    // Bounded candidate reasons now accompany the one focused goal; each
    // reason may cite its selected subgoal, but never an internal schema.
    assert!(message.len() < 4000, "{message}");
}

#[test]
fn negative_mdtest_failures_include_structured_proof_context() {
    for name in [
        "max_bad_ensure",
        "write_second_old_rejects_overwritten_cell",
        "resource_summary_requires_returned_write",
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(format!("{name}.md"));
        let source = std::fs::read_to_string(&path).unwrap();
        let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
        let click = fixture.click_source.as_deref().unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let error = verify_c0_sources(click, &sources).expect_err(name);
        let message = error.message();
        if name == "resource_summary_requires_returned_write" {
            assert!(
                message.contains("missing resource fact"),
                "{name}: {message}"
            );
            assert!(
                message.contains("missing resource fact `owns p[0]`"),
                "{name}: {message}"
            );
            assert!(
                message.contains("Requires produces owns p[0]"),
                "{name}: {message}"
            );
            assert!(
                message.contains("available resource facts: []"),
                "{name}: {message}"
            );
        } else {
            assert!(message.contains("goal:"), "{name}: {message}");
            assert!(message.contains("recent premises"), "{name}: {message}");
        }
        assert!(!message.contains("CMemory {"), "{name}: {message}");
    }
}

/// An undecided C `if` reported its two condition paths with the kernel
/// `Debug` of their facts. A condition whose load has not been named by a
/// load variable — the shape `list_count_live` reaches after its recursive
/// call — then carries the whole `CMemory` snapshot, blocks and heap
/// included, twice. That is the raw-state dump `AGENTS.md` names. Each path
/// is now spelled on its own line in the bounded source vocabulary, which is
/// what says which condition each arm assumes.
#[test]
fn undecided_c_branch_step_reports_its_paths_without_a_memory_dump() {
    let c_source = r#"
struct node {
    int32 value;
    unsigned long word;
};

int32 pick(struct node* node) {
    if ((node->word & 1) != 0) {
        return 1;
    }
    return 0;
}
"#;
    let click_source = r#"
verifying "pick.c";

resource node_storage(p: struct node*) {
    owns *p;
}


int32 pick(struct node* node) {
    requires node != 0;
    views node_storage(node);

    ensures 0 <= result;
} by {
    step();
    simp();
}
"#;
    let error = verify_c0_sources(click_source, &[("pick.c", c_source)]).unwrap_err();
    let message = error.message();
    assert!(
        message.contains("feasible condition paths"),
        "the step should report the undecided C `if`: {message}"
    );
    assert!(
        message.contains("condition path 0:") && message.contains("condition path 1:"),
        "each arm's assumption should be spelled on its own line: {message}"
    );
    assert!(!message.contains("CMemory {"), "{message}");
    assert!(!message.contains("CHeapMemory {"), "{message}");
    assert!(!message.contains("CBlock {"), "{message}");
    assert!(message.len() < 8000, "{message}");
}

#[test]
fn maybe_throwing_step_diagnostic_teaches_outcomes_syntax() {
    let call = crate::kernel::c_call("helper", Vec::new());
    let message =
        super::diagnostics::describe_multiple_statement_successors_guidance(&call, 2, true);

    assert!(
        message.contains("Use `outcomes` at this point"),
        "{message}"
    );
    assert!(message.contains("returned => { step(); }"), "{message}");
    assert!(message.contains("threw => { step(); }"), "{message}");
    assert!(
        message.contains("all\ncontract claims are closed"),
        "{message}"
    );
}

/// Two successors that both continue are an undecided branch inside an
/// inlined callee. `outcomes` has a `returned` and a `threw` arm and no way to
/// take either of those, so the refusal must not offer it.
#[test]
fn branch_split_step_diagnostic_does_not_offer_outcomes() {
    let call = crate::kernel::c_call("helper", Vec::new());
    let message =
        super::diagnostics::describe_multiple_statement_successors_guidance(&call, 2, false);

    assert!(message.is_empty(), "{message}");
}

/// The one-successor refusal used to print the `While` node with `Debug`,
/// which attaches the body, every lowered invariant and effect check, and
/// every resource spec to the message. A statement head is the statement's own
/// C spelling and nothing else.
#[test]
fn statement_head_names_the_guard_without_the_loop_node() {
    use crate::kernel::{
        c_and, c_assign, c_int32_literal, c_load, c_not_equal, c_variable, c_while,
    };

    let condition = c_and(
        c_not_equal(c_variable("a"), c_int32_literal(0)),
        c_not_equal(c_load(c_variable("p")), c_int32_literal(0)),
    );
    let body = c_assign("unmistakable_body_local", c_int32_literal(0));
    let loop_statement = c_while(condition, Vec::new(), body);
    let head = super::diagnostics::describe_c_statement_head(&loop_statement);

    assert_eq!(head, "while ((a != 0) && (*p != 0))");
    assert!(!head.contains("unmistakable_body_local"), "{head}");
    assert!(!head.contains("invariant_checks"), "{head}");

    // A guard spelled past the printer's byte budget is truncated rather than
    // allowed to set the size of the diagnostic.
    let mut wide = c_not_equal(c_variable("a"), c_int32_literal(0));
    for _ in 0..200 {
        wide = c_and(
            wide,
            c_not_equal(c_variable("another_long_operand_name"), c_int32_literal(0)),
        );
    }
    let wide_head = super::diagnostics::describe_c_statement_head(&c_while(
        wide,
        Vec::new(),
        c_assign("a", c_int32_literal(0)),
    ));
    assert!(wide_head.len() <= 512, "{}", wide_head.len());
    assert!(wide_head.ends_with('…'), "{wide_head}");
}

#[test]
fn loan_refusal_diagnostic_renders_only_its_selected_subject() {
    use crate::kernel::{Bitvector32Term, CMemoryRange, Pointer, PointerBlock, PointerOffsetTerm};
    use crate::kernel::{LoanRefusal, LoanRefusalOperation, LoanRefusalSubject};

    let pointer = Pointer {
        block: PointerBlock::Concrete("selected_resource".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let selected = CResourceFact::own_memory(CMemoryRange::new(
        pointer,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(4),
    ));
    let diagnostic = LoanRefusal::ActiveDependency.diagnostic_with_subject(
        LoanRefusalOperation::MemoryAccess,
        LoanRefusalSubject::for_resource(selected),
    );
    let rendered = super::diagnostics::describe_runtime_error(
        &crate::kernel::CRuntimeError::LoanRefusal(Box::new(diagnostic)),
        ParameterBinding::default(),
    );

    assert!(rendered.contains("selected resource"), "{rendered}");
    assert!(rendered.contains("selected_resource"), "{rendered}");
    assert!(!rendered.contains("unrelated_resource"), "{rendered}");
    assert!(rendered.len() < 1024, "{}", rendered.len());
}

#[test]
fn loan_refusal_diagnostic_renders_a_range_subject_without_ledger_state() {
    use crate::kernel::{Bitvector32Term, CMemoryRange, Pointer, PointerBlock, PointerOffsetTerm};
    use crate::kernel::{LoanRefusal, LoanRefusalOperation, LoanRefusalSubject};

    let range = CMemoryRange::new(
        Pointer {
            block: PointerBlock::Concrete("selected_range".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        },
        Bitvector32Term::Constant(1),
        Bitvector32Term::Constant(3),
    );
    let diagnostic = LoanRefusal::UnsupportedPartition.diagnostic_with_subject(
        LoanRefusalOperation::Plan,
        LoanRefusalSubject::for_range(range),
    );
    let rendered = super::diagnostics::describe_runtime_error(
        &crate::kernel::CRuntimeError::LoanRefusal(Box::new(diagnostic)),
        ParameterBinding::default(),
    );

    assert!(rendered.contains("selected range"), "{rendered}");
    assert!(rendered.contains("selected_range"), "{rendered}");
    assert!(!rendered.contains("CMemoryRange {"), "{rendered}");
    assert!(rendered.len() < 1024, "{}", rendered.len());
}

/// Two distinct loads over the same address used to render identically
/// (`left side evaluated to load(p[0]), right side evaluated to load(p[0])`),
/// which reads as an unprovable `x == x`. The message now reports each side's
/// surface spelling and which snapshot it reads, and appends the checked proof
/// context every other failed goal reports. It does not guess which step was
/// missing.
#[test]
fn identical_load_renders_name_distinct_snapshot_loads() {
    let c_source = r#"
            int32 sym_index_clobber(int32* p, int32 i) {
                p[i] = 7;
                return p[0];
            }
        "#;
    let click_source = r#"
            verifying "sym_index_clobber.c";

            int32 sym_index_clobber(int32* p, int32 i) {
                owns p[0..2];
                requires 0 <= i and i < 2;
                ensures result == old(p[0]) by auto;
            }
        "#;

    let error = verify_c0_sources(click_source, &[("sym_index_clobber.c", c_source)])
        .expect_err("a symbolically-indexed write must leave the old-value goal open");
    let message = error.message();
    assert!(
        message.contains("read the same address in different memory snapshots"),
        "{message}"
    );
    assert!(
        message.contains("`result` reads the outcome state"),
        "{message}"
    );
    assert!(
        message.contains("`old(p[0])` reads function entry"),
        "{message}"
    );
    assert!(message.contains("proof context for the goal:"), "{message}");
    assert!(
        message.contains("resource facts: [owns p[0..2]"),
        "{message}"
    );
    assert!(!message.contains("distinct kernel loads"), "{message}");
    assert!(!message.contains("left side evaluated to"), "{message}");
    assert!(
        !message.contains("unchanged by the writes in between"),
        "{message}"
    );
}

/// The store-cause renderer, driven directly at the two cases it now
/// distinguishes.
///
/// Separation is a question about bytes, not addresses, so a store wider than
/// the array's element must not be answered with an index inequality: it
/// covers the element it names and the one above it, and `i != j` leaves
/// `i == j + 1` open. The order it names instead is the one the gap rule
/// clears, and `mdtests/an_index_order_separates_a_narrow_read_from_a_wide_store.md`
/// is that order verifying. Where the store fits in an element the indexes
/// really are the undecided part, and that sentence is unchanged.
#[test]
fn a_store_wider_than_an_element_is_refused_by_bytes_not_by_index() {
    let byte_reach = super::diagnostics::store_cause_between_indexes_for_tests(
        "a",
        "i",
        "j",
        Some(4),
        4,
        Some(8),
    );
    assert_eq!(
        byte_reach,
        "the store to `a[j]` writes 8 bytes where `a` has 4-byte elements, so it covers the 2 \
         elements from `a[j]` up and `i != j` rules out only the first of them. State `i < j`, \
         which puts `a[i]` below every byte the store writes."
    );

    // A read that does not fit in an element either has no order to be put
    // below the store by, so none is offered. The widest-scalar fallback
    // reaches this arm too, which is why it may not promise a repair.
    let both_wide = super::diagnostics::store_cause_between_indexes_for_tests(
        "a",
        "i",
        "j",
        Some(4),
        8,
        Some(8),
    );
    assert_eq!(
        both_wide,
        "the store to `a[j]` writes 8 bytes where `a` has 4-byte elements, so it covers the 2 \
         elements from `a[j]` up and `i != j` rules out only the first of them. Only a stated \
         order between the indexes can separate them, and it has to put an access of at most 4 \
         bytes below the other."
    );

    // The undecided-index case, unregressed: a store that fits in the element
    // it names is separated by the index inequality, and that is what is
    // printed. Width unavailable falls here too, because a width nobody
    // recorded is not one a refusal may reason from.
    let undecided_index = "the store to `a[j]` may have written it. If `i` and `j` differ, state \
                           `i != j`.";
    assert_eq!(
        super::diagnostics::store_cause_between_indexes_for_tests(
            "a",
            "i",
            "j",
            Some(4),
            4,
            Some(4)
        ),
        undecided_index
    );
    assert_eq!(
        super::diagnostics::store_cause_between_indexes_for_tests("a", "i", "j", Some(4), 4, None),
        undecided_index
    );
    assert_eq!(
        super::diagnostics::store_cause_between_indexes_for_tests("a", "i", "j", None, 4, Some(8)),
        undecided_index
    );

    // An inequality the facts already state is not offered again: stating it
    // a second time cannot change what this check concludes.
    use crate::kernel::{Bitvector32Term, ConditionTerm, Proposition, Variable};
    let i = Bitvector32Term::Variable(Variable(1));
    let j = Bitvector32Term::Variable(Variable(2));
    let differ = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(j.clone()), Box::new(i.clone())),
        false,
    );
    assert_eq!(
        super::diagnostics::store_cause_between_indexes_with_facts_for_tests(
            "a",
            ("i", Some(i.clone())),
            ("j", Some(j.clone())),
            Some(4),
            4,
            Some(4),
            &[&differ],
        ),
        "the store to `a[j]` may have written it. `i != j` is already available, so stating \
         it again will not help."
    );
    let unrelated = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(i.clone()),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        false,
    );
    assert_eq!(
        super::diagnostics::store_cause_between_indexes_with_facts_for_tests(
            "a",
            ("i", Some(i)),
            ("j", Some(j)),
            Some(4),
            4,
            Some(4),
            &[&unrelated],
        ),
        undecided_index
    );
}

#[test]
fn empty_footprint_rejects_a_fact_aliased_write_and_effect_range() {
    let global = Pointer {
        block: "global:counter".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let alias = Pointer {
        block: PointerBlock::Symbolic(Variable(982_001)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = CMemory::new().with_block(global.block.clone(), 4);
    let after = before.clone().store(alias.clone(), int32(1));
    let pre_state = CState::new().with_memory(before.clone());
    let outcome = CFunctionOutcome::Return {
        value: int32(0),
        state: Box::new(CState::new().with_memory(after.clone())),
    };
    let aliases_global =
        Proposition::ConditionIs(ConditionTerm::pointer_equal(alias.clone(), global), true);
    let facts = [
        ExecutionPureFact::new(Proposition::CMemoryMutatesOnly {
            before: before.clone(),
            after: after.clone(),
            writes: vec![(alias.clone(), 4)],
        }),
        ExecutionPureFact::new(Proposition::CMemoryEffectSummary {
            before,
            after,
            mutable_ranges: vec![CMemoryRange::new(
                alias,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )],
        }),
    ];
    for fact in &facts {
        super::checking::prove_empty_write_footprint(
            "aliased.implicit_effect",
            0,
            std::slice::from_ref(fact),
            &PureFactList::default(),
            ParameterBinding::default(),
            &pre_state,
            &outcome,
        )
        .expect("the symbolic spelling alone does not name preexisting storage");
        let error = super::checking::prove_empty_write_footprint(
            "aliased.implicit_effect",
            0,
            std::slice::from_ref(fact),
            &PureFactList::from(vec![aliases_global.clone()]),
            ParameterBinding::default(),
            &pre_state,
            &outcome,
        )
        .expect_err("a fact-aliased write reaches the preexisting global");
        assert!(error.message().contains("outside the mutable footprint"));
    }
}

/// A conditional term's guard is spelled as the comparison it means. The
/// kernel states a 32-bit unsigned comparison as a signed one over operands
/// with their sign bit flipped; rendered context-free, that used to read as
/// the raw bias.
#[test]
fn a_conditional_term_spells_its_unsigned_guard() {
    let x = Bitvector32Term::Variable(crate::kernel::Variable(7));
    let term = Bitvector32Term::If {
        condition: Box::new(ConditionTerm::unsigned_less_than(
            x.clone(),
            Bitvector32Term::Constant(4),
        )),
        then_term: Box::new(x),
        else_term: Box::new(Bitvector32Term::Constant(5)),
    };
    let rendered = super::diagnostics::describe_bitvector(&term);
    assert!(rendered.contains(" < 4 (unsigned)"), "{rendered}");
    assert!(!rendered.contains('^'), "{rendered}");
}

#[test]
fn missing_mutex_use_names_the_required_resource_without_loan_internals() {
    let mutex = crate::kernel::Pointer {
        block: "selected_mutex".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let rendered = super::diagnostics::describe_runtime_error(
        &crate::kernel::CRuntimeError::MissingMutexUse {
            mutex: mutex.clone(),
        },
        ParameterBinding::default(),
    );
    let owner = super::diagnostics::describe_runtime_error(
        &crate::kernel::CRuntimeError::MissingMutexLive { mutex },
        ParameterBinding::default(),
    );
    assert_eq!(rendered, owner.replace("mutex_live", "mutex_use"));
    assert!(
        rendered.starts_with("Requires owns mutex_use("),
        "{rendered}"
    );
    assert!(rendered.contains("selected_mutex"), "{rendered}");
    assert!(!rendered.contains("Loan"), "{rendered}");
}

/// C source whose refusals each name one statement: a struct-field store
/// past its array, a signed overflow, and a call whose precondition the
/// caller cannot show. `inc` verifies.
const SITED_C_SOURCE: &str = "struct item { int32 x; int32 y; };

int32 store() {
    struct item items[4];
    int32 i;
    i = 0;
    while (i < 5) {
        items[i].x = 7;   // the field store
        i = i + 1;
    }
    return 0;
}

int32 add(int32 a, int32 b) {
    int32 total;
    total = a + b;
    return total;
}

int32 callee(int32 n) {
    return n;
}

int32 caller(int32 n) {
    int32 r;
    r = callee(n) + 1;
    return r;
}

int32 inc(int32 n) {
    return n + 1;
}
";

/// `SITED_C_SOURCE` written elsewhere in its file: three more lines above
/// it, every line indented, and a comment after each `{`.
fn shifted_sited_c_source() -> String {
    let mut shifted = String::from("// moved down\n\n/* and over */\n");
    for line in SITED_C_SOURCE.lines() {
        shifted.push_str("  ");
        shifted.push_str(line);
        if line.ends_with('{') {
            shifted.push_str(" // opens");
        }
        shifted.push('\n');
    }
    shifted
}

/// `message` without its `C statement at` lines, and those lines.
fn split_statement_sites(message: &str) -> (String, Vec<String>) {
    let mut rest = Vec::new();
    let mut sites = Vec::new();
    for line in message.split('\n') {
        if line.starts_with("  C statement at ") {
            sites.push(line.to_string());
        } else {
            rest.push(line);
        }
    }
    (rest.join("\n"), sites)
}

/// A statement's site is diagnostics only. The same C written at other
/// lines and columns, with other comments, parses to equal C0 and kernel
/// functions and verifies with the same work and the same messages, apart
/// from the `C statement at` line each refusal gains, which names the line
/// and column the statement moved to and quotes it without its comment.
#[test]
fn statement_sites_change_nothing_but_the_location_line() {
    let shifted = shifted_sited_c_source();
    let original = crate::languages::c::syntax::parse_functions(SITED_C_SOURCE).unwrap();
    let moved = crate::languages::c::syntax::parse_functions(&shifted).unwrap();
    assert_eq!(original, moved);
    for (original, moved) in original.iter().zip(&moved) {
        assert_eq!(original.to_kernel_function(), moved.to_kernel_function());
        assert_eq!(format!("{original:?}"), format!("{moved:?}"));
    }

    let header = "verifying \"f.c\";\n";
    let cases = [
        (
            "int32 store() {\n    ensures result == 0;\n} by {\n    step(); step(); step();\n    loop { decreases 5 - i; invariant i >= 0; invariant i <= 4; }\n    execute(); simp();\n}\n",
            Some(("f.c:8:9: `items[i].x = 7;`", "f.c:11:11: `items[i].x = 7;`")),
        ),
        (
            "int32 add(int32 a, int32 b) {\n    ensures result == a + b;\n} by {\n    step(); step(); step(); simp();\n}\n",
            Some(("f.c:16:5: `total = a + b;`", "f.c:19:7: `total = a + b;`")),
        ),
        (
            "int32 callee(int32 n) {\n    requires n >= 0;\n    ensures result == n;\n}\nint32 caller(int32 n) {\n    ensures result == n + 1;\n} by {\n    step(); step(); step(); simp();\n}\n",
            Some((
                "f.c:26:5: `r = callee(n) + 1;`",
                "f.c:29:7: `r = callee(n) + 1;`",
            )),
        ),
        (
            "int32 inc(int32 n) {\n    requires n <= 100;\n    ensures result == n + 1;\n} by {\n    step(); simp();\n}\n",
            None,
        ),
    ];
    for (proof, expected_sites) in cases {
        let click_source = format!("{header}{proof}");
        // The first verification in a process also builds shared caches;
        // both measured runs come after it.
        let _ = verify_c0_sources(&click_source, &[("f.c", SITED_C_SOURCE)]);
        let (original, original_work) = crate::instrumentation::measure_deterministic_work(|| {
            verify_c0_sources(&click_source, &[("f.c", SITED_C_SOURCE)])
        });
        let (moved, moved_work) = crate::instrumentation::measure_deterministic_work(|| {
            verify_c0_sources(&click_source, &[("f.c", &shifted)])
        });
        assert!(original_work > 0, "{proof}");
        assert_eq!(original_work, moved_work, "{proof}");
        match expected_sites {
            None => {
                original.unwrap();
                moved.unwrap();
            }
            Some((original_site, moved_site)) => {
                let original = original.unwrap_err();
                let moved = moved.unwrap_err();
                let (original_rest, original_sites) = split_statement_sites(original.message());
                let (moved_rest, moved_sites) = split_statement_sites(moved.message());
                assert_eq!(original_rest, moved_rest);
                assert_eq!(
                    original_sites,
                    [format!("  C statement at {original_site}")],
                    "{}",
                    original.message()
                );
                assert_eq!(
                    moved_sites,
                    [format!("  C statement at {moved_site}")],
                    "{}",
                    moved.message()
                );
            }
        }
    }
}

/// A loop's generated closer that fails reports the open member and the
/// goal, attributed to the `loop` tactic. The premises and search candidates
/// stay in the trace; they are not folded into the summary and reported as
/// a line per colon.
#[test]
fn failed_generated_loop_closer_reports_a_short_summary_at_the_loop_tactic() {
    let c_source = r#"
        int32 settle(int32 state) {
            while (state > 0) {
                state = state;
            }
            return 0;
        }
    "#;
    let click_source = r#"
        verifying "settle.c";

        int32 settle(int32 state) {
            requires state >= 0;
            ensures result == 0;
        } by {
            loop {
                decreases state;
                invariant state >= 0;
            }
            execute();
            simp();
        }
    "#;
    let error = verify_c0_sources(click_source, &[("settle.c", c_source)])
        .expect_err("a loop whose measure does not decrease is refused");
    let (report, context) = error.concise_report_parts();
    assert!(report.contains("`state < state` remained open"), "{report}");
    assert!(report.lines().count() <= 4, "{report}");
    for internal in ["stage", "search candidates", "18446744073709551615"] {
        assert!(!report.contains(internal), "{report}");
    }
    assert!(
        context.iter().any(|line| line.starts_with("goal: ")),
        "{context:?}"
    );
    assert_eq!(error.proof_source_tactic_path(), Some(&[0][..]));
}

/// A pure theorem's accepted path is retained for a trace, each written
/// tactic addressed by its source occurrence, and tracing it verifies
/// neither another theorem nor a C function.
#[test]
fn a_passing_theorem_retains_its_accepted_trace_path() {
    let source = r#"verifying "f.c";
theorem good(x: int32, y: int32) {
    requires x == y;
    ensures y == x by {
        have y == x by { simp(); }
        assumption();
    }
}
theorem split(x: int32) {
    requires x == 1 or x == 2;
    ensures x >= 1 by {
        cases {
            x == 1 => {
                rewrite(x == 1);
                normalize();
            }
            x == 2 => {
                rewrite(x == 2);
                normalize();
            }
        }
    }
}
theorem unproved(x: int32) { ensures x == 0 by { normalize(); } }
int32 f() { ensures result == 2; } by { step(); simp(); }
"#;
    let project = ClickProject::new(
        "entry.click",
        [ClickModuleSource::new("entry.click", source, [])],
    );
    let c = [("f.c", "int f(void) { return 1; }")];
    let locate = |claim: &str, path: &[usize]| {
        let outer = project_tactic_source_position(
            &project,
            &ProgramInputs::Bundle(c.to_vec()),
            claim,
            path[0],
        )
        .ok()?;
        let position = if path.len() == 1 {
            outer
        } else {
            nested_tactic_source_position(source, &outer, &path[1..]).ok()?
        };
        Some((format!("tactic@{}", position.line), position))
    };
    let arm = |claim: &str, path: &[usize], target: &SourcePosition| {
        let (_, branch) = locate(claim, path)?;
        tactic_arm_containing_position(source, &branch, target)
            .ok()
            .flatten()
    };
    with_proof_trace("good", || {
        verify_project_theorem(&project, &ProgramInputs::Bundle(c.to_vec()), "good").unwrap();
        let trace = accepted_proof_trace(&locate, &arm, &|_, _, _| false, None).unwrap();
        assert_eq!(
            trace,
            "proof trace (checked tactics and branch facts):\ntactic@5: have y == x\n  adds: y == x\ntactic@6: assumption()"
        );
    });
    with_proof_trace("split", || {
        verify_project_theorem(&project, &ProgramInputs::Bundle(c.to_vec()), "split").unwrap();
        let whole = accepted_proof_trace(&locate, &arm, &|_, _, _| false, None).unwrap();
        assert!(whole.ends_with("\ntactic@12: cases"), "{whole}");
        let right = accepted_proof_trace(
            &locate,
            &arm,
            &|_, _, _| false,
            Some(&SourcePosition::new(19, 17)),
        )
        .unwrap();
        assert!(
            right.ends_with(
                "\ntactic@12: cases (right arm)\n  adds: x == 2\n  tactic@18: rewrite\n  tactic@19: normalize()"
            ),
            "{right}"
        );
        assert!(!right.contains("x == 1"), "{right}");
    });
    // The theorem that fails reports the tactic it wrote.
    let error = verify_project_theorem(&project, &ProgramInputs::Bundle(c.to_vec()), "unproved")
        .unwrap_err();
    assert_eq!(
        error.proof_source_site(),
        Some(("unproved.ensures_0", &[0][..]))
    );
}

fn folded_child_loop_fixture() -> crate::cli::MdTest {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/loop_invariant_old_model_of_an_instance_folded_into_a_parent.md");
    crate::cli::parse_mdtest(&path, &std::fs::read_to_string(&path).unwrap()).unwrap()
}

#[test]
fn folded_child_loop_field_refusal_names_the_fold_and_a_verified_remedy() {
    let fixture = folded_child_loop_fixture();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let error = verify_c0_sources(fixture.click_source.as_deref().unwrap(), &sources).unwrap_err();
    assert!(
        error
            .message()
            .contains("consumed as child `inner` when `w` was folded"),
        "{error:?}"
    );
    assert!(
        error.message().contains("match it before the loop"),
        "{error:?}"
    );
    assert!(!error.message().contains("unfold(c)"), "{error:?}");
    assert!(!error.message().contains("let { model:"), "{error:?}");
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/loop_invariant_binds_model_from_a_folded_parent.md");
    let repaired =
        crate::cli::parse_mdtest(&path, &std::fs::read_to_string(&path).unwrap()).unwrap();
    assert_eq!(fixture.c_sources, repaired.c_sources);
    verify_c0_sources(repaired.click_source.as_deref().unwrap(), &sources)
        .unwrap_or_else(|error| panic!("the suggested payload binding must verify: {error:?}"));
}

#[test]
fn unfolded_algebraic_field_refusal_never_suggests_a_c_field_pattern() {
    let fixture = folded_child_loop_fixture();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let mut click = fixture.click_source.unwrap();
    let loop_start = click.find("    loop {").unwrap();
    click.truncate(loop_start);
    click.push_str(
        r#"
        match w.model {
            Wrap::Wrap(entry_model) => {
                let { inner: child } = unfold(w);
                have w.model == Wrap::Wrap(entry_model) by { simp(); }
            },
        }
    }
    "#,
    );
    let error = verify_c0_sources(&click, &sources).unwrap_err();
    assert!(
        error.message().contains("`unfold(w)` consumed it"),
        "{error:?}"
    );
    assert!(
        error
            .message()
            .contains("an unfold pattern cannot bind an algebraic field"),
        "{error:?}"
    );
    assert!(!error.message().contains("let { model:"), "{error:?}");
}

#[test]
fn unheld_field_without_a_checked_consumption_does_not_invent_one() {
    let proposition = ClickProposition::Comparison {
        operator: ComparisonOperator::Equal,
        left: ContractExpression::ResourceField(ResourceFieldAccess {
            owner: "absent".into(),
            resource_name: "cell".into(),
            identity: Variable(999),
            children: vec![],
            field: "rank".into(),
            field_index: 0,
            click_type: Some(ClickType::C(C0Type::Int32)),
        }),
        right: ContractExpression::CFragment(CExpression::Value(crate::kernel::int32(0))),
    };
    let message = crate::surface::diagnostics::describe_consumed_instance_field_read(
        &proposition,
        &CState::new(),
        false,
    )
    .unwrap();
    assert!(
        message.contains("no checked fold or unfold of this instance is recorded"),
        "{message}"
    );
    assert!(!message.contains("consumed it"), "{message}");
}

#[test]
fn source_unknown_local_pointer_diagnostics_identify_byte_units() {
    use crate::kernel::{
        Bitvector32Term, CMemoryRange, CPointerValue, CType, Pointer, PointerBlock,
        PointerOffsetTerm,
    };
    let base = Pointer {
        block: PointerBlock::Concrete("unknown".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new().with_local(
        "cursor",
        CValue::Pointer(CPointerValue::new(base.clone(), CType::Int32Pointer)),
    );
    let (parameters, arguments) = super::diagnostics::local_naming_tables_with_source(&state, None);
    let range = CMemoryRange::new(
        base,
        Bitvector32Term::Constant(1),
        Bitvector32Term::Constant(2),
    );
    assert_eq!(
        super::diagnostics::describe_memory_range(
            &range,
            ParameterBinding::new(&parameters, &arguments)
        ),
        "((char *)cursor)[4..8]"
    );
}

#[test]
fn read_only_wide_index_diagnostic_requests_equality_without_inventing_a_store() {
    let source = "int32 last(int32* data, uint64 length) { return *(data + (length - 1ULL)); }";
    let sidecar = r#"
verifying "last.c";
int32 last(int32* data, uint64 length) {
    owns data[0..1];
    requires length == 1u64;
    ensures result == old(data[0]);
} by { execute(); simp(); }
"#;
    // Exact wide-index constants now resolve without a manual rewrite.
    verify_c0_sources(sidecar, &[("last.c", source)]).unwrap();
    let ambiguous = sidecar
        .replace("owns data[0..1];", "owns data[0..2];")
        .replace("requires length == 1u64;", "requires length == 2u64;");
    let error = match verify_c0_sources(&ambiguous, &[("last.c", source)]) {
        Err(error) => error,
        Ok(_) => panic!("distinct readable addresses do not establish equal values"),
    };
    let message = error.message();
    assert!(message.contains("index/address"), "{message}");
    assert!(message.contains("same recorded memory"), "{message}");
    assert!(!message.contains("the store to"), "{message}");
    assert!(
        !message.contains("state `(length - 1u64) != 0`"),
        "{message}"
    );
    // The index is resolved while the function runs, so the claim at exit
    // no longer mentions `length` and there is nothing left to rewrite.
}

#[test]
fn unfinished_callback_scripts_report_the_missing_authority_to_continue() {
    for (fixture_name, expected) in [
        (
            "rb_augment_callbacks_helper_rejects_changed_cell.md",
            Some("no contract fact for the function pointer `augment->copy`"),
        ),
        (
            "rb_augment_callbacks_helper_consumes_suite.md",
            Some("missing resource fact `views augment->copy`"),
        ),
        ("rb_augment_callbacks_helper_owns.md", None),
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(fixture_name);
        let fixture = crate::cli::read_mdtest(&path).unwrap();
        let mut source = fixture.click_source.unwrap();
        if expected.is_none() {
            // Three lowered operations per callback and the implicit void return.
            source = source.replace("execute();", &"step(); ".repeat(10));
        }
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let result = verify_c0_sources(&source, &sources);
        if let Some(expected) = expected {
            let error = result.unwrap_err();
            assert!(
                error.message().contains(expected),
                "{fixture_name}: {}",
                error.message()
            );
            assert!(
                !error.message().contains("cannot yet certify"),
                "{}",
                error.message()
            );
            let report = error.concise_report();
            assert!(report.contains(expected), "{fixture_name}: {report}");
            assert!(
                report.contains("the proof stops before this callback"),
                "{fixture_name}: {report}"
            );
        } else {
            result.unwrap_or_else(|error| panic!("{fixture_name}: {}", error.message()));
            let named = source.replace(
                &"step(); ".repeat(10),
                "step(); step(); step(Propagate); step(); step(); step(Copy); step(); step(); step(Rotate); step();",
            );
            verify_c0_sources(&named, &sources)
                .unwrap_or_else(|error| panic!("named callback steps: {}", error.message()));
            let smart = source.replace(&"step(); ".repeat(10), "execute();");
            let expanded =
                expand_c0_claim_source(&smart, &sources, "erase_augmented", CProofClaim::Grouped)
                    .unwrap();
            verify_c0_sources(&expanded, &sources)
                .unwrap_or_else(|error| panic!("expanded callbacks: {}", error.message()));
        }
    }
}

#[test]
fn unfinished_callback_scripts_keep_a_bounded_diagnostic_preview() {
    for fixture_name in [
        "rb_augment_callbacks_helper_owns.md",
        "rb_augment_callbacks_helper_rejects_changed_cell.md",
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(fixture_name);
        let fixture = crate::cli::read_mdtest(&path).unwrap();
        let source = fixture.click_source.unwrap();
        let (source, c_sources) = if fixture_name.ends_with("owns.md") {
            // A successful diagnostic continuation still cannot certify an
            // exhausted script: these steps stop after the first callback.
            (
                source
                    .replace("execute();", "step(); step(); step();")
                    .replace("simp();", ""),
                fixture.c_sources,
            )
        } else {
            // The missing Copy fact lies far beyond the bounded preview.
            // Keep the written proof and every other C statement unchanged.
            let c_sources = fixture
                .c_sources
                .into_iter()
                .map(|(name, c)| {
                    (
                        name,
                        c.replace(
                            "    augment->rotate(node, parent);\n",
                            &"    augment->rotate(node, parent);\n".repeat(16),
                        ),
                    )
                })
                .collect();
            (source, c_sources)
        };
        let sources = c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let error = verify_c0_sources(&source, &sources).unwrap_err();
        assert!(
            error.message().contains("proof stops before function exit"),
            "{fixture_name}: {}",
            error.message()
        );
    }
}

/// A member offset that is not a whole struct stride used to be spelled
/// through an unrelated int32 pointer, inventing an anchor/p alias repair.
#[test]
fn struct_field_frame_failure_names_the_read_and_written_members() {
    let c_source = r#"
        struct node { uint64 tag; struct node *right; struct node *left; };
        struct node *change(struct node *p, int32 j, int32 *anchor) {
            p[j].left = 0;
            return p[0].left;
        }
    "#;
    let source = r#"
        verifying "field.c";
        struct node* change(struct node* p, int32 j, int32* anchor) {
            owns p[0..2];
            owns *anchor;
            requires 0 <= j;
            requires j < 2;
            ensures result == old(p[0].left);
        } by {
            step();
            have p[0].left == old(p[0].left) by { simp(); }
            execute(); simp();
        }
    "#;
    let error = verify_c0_sources(source, &[("field.c", c_source)])
        .expect_err("the indexed store may overwrite the first member");
    let message = error.message();
    assert!(message.contains("`p->left` may have changed"), "{message}");
    assert!(
        message.contains("the store to `p[j].left` may have written `p->left`"),
        "{message}"
    );
    let reason = message.split("\n  stage:").next().unwrap();
    assert!(!reason.contains("anchor["), "{message}");
    assert!(!message.contains("may point into"), "{message}");
}

#[test]
fn pure_theorem_tactics_emit_claims_and_nested_written_source_paths() {
    use crate::instrumentation::{VerificationEvent, collect};
    let source = r#"theorem nested(x: int32) {
        requires x <= 100;
        ensures x <= 1000 by {
            have x <= 1000 by { arithmetic() using { x <= 100; } }
            assumption();
        }
        ensures x == x by { normalize(); }
    }"#;
    let (result, events) = collect(|| verify_click_theorems(source));
    assert_eq!(result.unwrap().len(), 2);
    assert_eq!(
        events
            .iter()
            .filter(|event| matches!(event, VerificationEvent::ProofClaimFinished { .. }))
            .count(),
        2
    );
    let starts: Vec<_> = events
        .iter()
        .filter_map(|event| match event {
            VerificationEvent::TacticStarted(tactic) => Some(tactic),
            _ => None,
        })
        .collect();
    assert!(
        starts
            .iter()
            .any(|tactic| tactic.claim == "nested.ensures_0"
                && tactic.source_tactic_path.as_deref() == Some(&[0, 0])
                && tactic.class == "smart")
    );
    assert!(
        starts
            .iter()
            .any(|tactic| tactic.claim == "nested.ensures_1"
                && tactic.source_tactic_path.as_deref() == Some(&[0])
                && tactic.class == "simple")
    );
    assert!(events.iter().any(|event| matches!(event, VerificationEvent::FunctionFinished { name, .. } if name == "nested")));
}

#[test]
fn pure_theorem_arithmetic_obeys_its_tactic_budget() {
    use crate::instrumentation::{
        TacticWorkLimits, VerificationEvent, collect, with_tactic_work_limits,
    };
    let source = "theorem bound(x: int32) { requires x <= 100; ensures x <= 1000 by { arithmetic() using { x <= 100; } } }";
    let (result, events) = collect(|| {
        with_tactic_work_limits(
            TacticWorkLimits {
                simple: 1,
                smart: 1,
                control: 1,
            },
            || verify_click_theorems(source),
        )
    });
    let error = result.expect_err("a pure theorem bypassed its tactic work budget");
    assert!(error.message().contains("budget"), "{}", error.message());
    assert!(
        events.iter().any(|event| matches!(event,
            VerificationEvent::TacticWorkBudgetExceeded { tactic, .. }
            if tactic.claim == "bound.ensures_0" && tactic.class == "smart"
                && tactic.source_tactic_path.as_deref() == Some(&[0])
        )),
        "{events:?}"
    );
}

#[test]
fn wide_conjunction_expansion_stays_parseable_and_checked() {
    let conjuncts: Vec<_> = (1..=40).map(|i| format!("x <= {i}")).collect();
    let source = format!(
        "theorem wide(x: int32) {{ requires x <= 0; ensures {} by {{ simp(); }} }}",
        conjuncts.join(" and ")
    );
    verify_click_theorems(&source).unwrap();
    let expanded =
        crate::surface::expand_c0_claim_source_by_label(&source, &[], "wide.ensures_0").unwrap();
    verify_click_theorems(&expanded).unwrap();
    assert!(expanded.contains("have "), "{expanded}");
    let invalid = expanded.replacen("requires x <= 0;", "requires x <= 2;", 1);
    assert!(verify_click_theorems(&invalid).is_err());
}

#[test]
fn pure_theorem_generic_and_structural_induction_emit_written_tactics() {
    use crate::instrumentation::{VerificationEvent, collect};
    let source = r#"
    spec enum TestList<T> { Nil, Cons(T, TestList<T>), }
    theorem reflexive<T>(x: T) { ensures x == x by { normalize(); } }
    theorem induction_shape(xs: TestList<int32>) {
        ensures xs == xs by {
            induct(xs) as ih {
                TestList::Nil => { normalize(); }
                TestList::Cons(head, tail) => { apply(ih(tail)); normalize(); }
            }
        }
    }"#;
    let (result, events) = collect(|| verify_click_theorems(source));
    assert_eq!(result.unwrap().len(), 2);
    assert!(events.iter().any(|event| matches!(event,
        VerificationEvent::TacticStarted(tactic) if tactic.claim == "reflexive.ensures_0"
            && tactic.class == "simple" && tactic.source_tactic_path.as_deref() == Some(&[0])
    )));
    assert!(events.iter().any(|event| matches!(event,
        VerificationEvent::TacticStarted(tactic) if tactic.claim == "induction_shape.ensures_0"
            && tactic.class == "control" && tactic.source_tactic_path.as_deref() == Some(&[0])
    )));
    assert!(events.iter().any(|event| matches!(event,
        VerificationEvent::TacticStarted(tactic) if tactic.claim == "induction_shape.ensures_0"
            && tactic.source_tactic_path.as_deref() == Some(&[2])
    )));
}

#[test]
#[ignore = "nightly: wide uint64 theorem tactic attribution and bounded work"]
fn pure_theorem_wide_arithmetic_has_attributed_work_at_growing_sizes() {
    use crate::instrumentation::{VerificationEvent, collect};
    for size in [8, 16, 32] {
        let expression = format!("x{}", " + 1u64".repeat(size));
        let source = format!(
            "theorem wide(x: uint64) {{ requires x <= 100u64; ensures {expression} <= 1000u64 by {{ arithmetic() using {{ x <= 100u64; }} }} }}"
        );
        let (result, events) = collect(|| verify_click_theorems(&source));
        if let Err(error) = result {
            assert!(
                error.message().contains("budget exhausted"),
                "size {size}: {}",
                error.message()
            );
        }
        assert!(
            events.iter().any(|event| matches!(event,
                VerificationEvent::TacticStarted(tactic) if tactic.claim == "wide.ensures_0"
                    && tactic.class == "smart" && tactic.source_tactic_path.as_deref() == Some(&[0])
            )),
            "size {size}: {events:?}"
        );
        assert!(events.iter().any(|event| matches!(event,
            VerificationEvent::TacticFinished { tactic, work, .. } if tactic.claim == "wide.ensures_0" && *work > 0
        ) || matches!(event,
            VerificationEvent::TacticWorkBudgetExceeded { tactic, used, .. } if tactic.claim == "wide.ensures_0" && *used > 0
        )), "size {size}: {events:?}");
    }
}

fn wide_loop_invariant_fixture(size: usize) -> (String, String) {
    let source =
        "void run(int total) { int remaining = total; while (0 < remaining) { remaining--; } }";
    // Most members are exact transported premises, so this checks generated
    // bundle structure without spending its budget searching for many bounds.
    // The distinct last member lets the negative check detect a lost leaf.
    let invariants: String = (0..size)
        .map(|i| {
            format!(
                "invariant total <= {};\n",
                if i + 1 == size { 1000 + i } else { 1000 }
            )
        })
        .collect();
    let proof = format!(
        r#"verifying "bundle.c";
void run(int32 total) {{ requires 0 <= total; requires total <= 1000; ensures 0 <= total; }} by {{
 step(); step();
 loop {{
  decreases remaining;
  invariant 0 <= remaining;
  invariant remaining <= total;
  {invariants}
  preserve by {{ step(); close_invariants by {{ simp(); }} }}
 }}
 execute(); simp();
}}
"#
    );
    (source.to_owned(), proof)
}

#[test]
#[ignore = "nightly: 14s whole wide loop expansion and negative recheck"]
fn wide_loop_invariant_bundle_expands_without_dropping_members() {
    let (source, proof) = wide_loop_invariant_fixture(40);
    let sources = [("bundle.c", source.as_str())];
    verify_c0_sources(&proof, &sources).unwrap();
    let expanded =
        crate::surface::expand_c0_claim_source_by_label(&proof, &sources, "run.contract").unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
    let invalid = expanded.replacen("invariant total <= 1039;", "invariant total <= -1;", 1);
    assert_ne!(invalid, expanded);
    assert!(verify_c0_sources(&invalid, &sources).is_err());
}

#[test]
#[ignore = "nightly: growing generated loop-bundle expansion and checked work"]
fn wide_loop_invariant_bundle_expansion_work_scales_with_members() {
    let mut samples = Vec::new();
    for size in [32, 64, 128] {
        eprintln!("wide loop bundle size {size}: verify");
        let (source, proof) = wide_loop_invariant_fixture(size);
        let sources = [("bundle.c", source.as_str())];
        verify_c0_sources(&proof, &sources).unwrap();
        let (expanded, work) = crate::instrumentation::measure_deterministic_work(|| {
            eprintln!("wide loop bundle size {size}: expand");
            crate::surface::expand_c0_claim_source_by_label(&proof, &sources, "run.contract")
        });
        let expanded = expanded.unwrap();
        eprintln!("wide loop bundle size {size}: recheck ({work} units)");
        verify_c0_sources(&expanded, &sources).unwrap();
        assert!(work > 0);
        samples.push((size, work));
    }
    // Quadrupling input allows the logarithmic bundle-indexing factor and
    // fixed setup, but rejects quadratic expansion/checking growth.
    assert!(samples[2].1 <= samples[0].1 * 6, "{samples:?}");
}

// Default theorem search is measured and bounded without inventing a written
// source occurrence; the CLI declaration-location regression covers failures.
#[test]
fn implicit_theorem_search_is_timed_without_a_written_tactic_path() {
    use crate::instrumentation::{VerificationEvent, collect};
    let source = "theorem implicit(x: int32) { requires x <= 1; ensures x <= 2; }";
    let (result, events) = collect(|| verify_click_theorems(source));
    assert_eq!(result.unwrap().len(), 1);
    let starts: Vec<_> = events
        .iter()
        .filter_map(|event| match event {
            VerificationEvent::TacticStarted(tactic) => Some(tactic),
            _ => None,
        })
        .collect();
    assert_eq!(starts.len(), 1);
    assert_eq!(starts[0].class, "smart");
    assert_eq!(starts[0].tactic_name, "simp");
    assert_eq!(starts[0].source_tactic_path, None);
    assert!(events.iter().any(|event| matches!(event,
        VerificationEvent::ProofClaimFinished { claim, .. } if claim == "implicit.ensures_0"
    )));
}

#[test]
fn linear_function_proofs_execute_once_at_multiple_sizes() {
    use crate::instrumentation::{VerificationEvent, collect};
    for size in [16, 64, 256] {
        let premises = "have 0 == 0 by { normalize(); }\n".repeat(size);
        let source = format!(
            "verifying \"f.c\"; int32 f() {{ ensures result == 0; }} by {{ {premises} execute(); simp(); }}"
        );
        let (result, events) =
            collect(|| verify_c0_sources(&source, &[("f.c", "int32 f() { return 0; }")]));
        result.unwrap();
        let executions = events
            .iter()
            .filter(|event| {
                matches!(event,
                    VerificationEvent::TacticStarted(tactic) if tactic.tactic_name == "execute"
                )
            })
            .count();
        assert_eq!(executions, 1, "linear proof with {size} premises");
    }
}

/// A real child overwrite must report the exact rejected slot and null
/// argument without suggesting that a missing equality is a verifier bug.
#[test]
fn child_argument_trace_reports_the_rejected_pair() {
    let c = "struct node { struct node *left; struct node *right; }; void f(struct node *p) { p->right = 0; }";
    let source = r#"
verifying "f.c";
spec enum Tree { Empty, Node(struct node*, struct node*, Tree, Tree) }
resource tree(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(id, link, lm, rm) => {
            owns p->left; owns p->right;
            fact p->right == link;
            owns left: tree(p->left); owns right: tree(p->right);
            fact p != 0; fact p == id;
            fact left.model == lm; fact right.model == rm;
        },
    }
}
void f(struct node* p) {
    owns t: tree(p);
    requires t.model != Tree::Empty;
    ensures t.model == old(t.model);
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, link, lm, rm) => {
            let { left: l, right: r } = unfold(t);
            mark before_store;
            have p->right == link by { assumption(); }
            step();
            let t = fold(tree(p), { model: Tree::Node(id, link, lm, rm) }, { left: l, right: r });
            execute(); simp();
        },
    }
}
"#;
    let ordinary = verify_c0_sources(source, &[("f.c", c)]).unwrap_err();
    assert!(
        ordinary
            .message()
            .contains("argument 1 equality is not established")
    );
    // The ordinary message spells its facts in source terms, with no
    // kernel snapshot or value labels to define.
    assert!(
        !ordinary.message().contains("snapshot#") && !ordinary.message().contains("value#"),
        "{}",
        ordinary.message()
    );
    with_proof_trace("f", || {
        let error = verify_c0_sources(source, &[("f.c", c)]).unwrap_err();
        let report = error.trace_context_report().unwrap();
        assert!(report.contains("child `right`, argument 1"), "{report}");
        assert!(report.contains("supplied: at("), "{report}");
        assert!(report.contains("required: 0"), "{report}");
        assert!(
            report.contains("at(statement(1).entry, p)->right"),
            "{report}"
        );
        let have = report.split("have p->right == link").nth(1).unwrap();
        let added = have.lines().find(|line| line.contains("adds")).unwrap();
        assert!(
            added.contains("value#") && added.contains("link"),
            "{report}"
        );
        assert!(!report.contains("Missing:"), "{report}");
    });
}

/// Smart execution must record the same checked call facts as written steps,
/// even when the later postcondition cannot be proved.
#[test]
fn execute_failure_trace_retains_checked_call_facts() {
    let c = "int helper(void) { return 1; } int f(void) { return helper(); }";
    for execution in ["execute();", "step(); step();"] {
        let source = format!(
            "verifying \"f.c\"; int32 helper() {{ ensures result == 1; }} by {{ execute(); simp(); }} \
             int32 f() {{ ensures result == 2; }} by {{ {execution} simp(); }}"
        );
        with_proof_trace("f", || {
            let error = verify_c0_sources(&source, &[("f.c", c)])
                .expect_err("the intentionally false postcondition must fail");
            let trace = error.trace_context_report().expect("failure trace");
            assert!(!trace.contains("<no checked simple steps"), "{trace}");
            assert!(trace.contains("step(helper("), "{trace}");
            assert!(trace.contains("adds"), "{trace}");
            assert!(
                trace.contains("== 1") || trace.contains(", 1) is true"),
                "{trace}"
            );
        });
    }
}

/// A parent without fields that holds a child with fields keeps a hidden
/// record, and its fact list is not the surface body's. A refused fold names
/// the fact it could not establish by the declaration's own spelling, in the
/// summary and in the trailer alike.
#[test]
fn fold_over_a_hidden_record_names_the_failed_fact() {
    let c = "struct cell { int32 value; }; struct pair { struct cell* a; int32 n; }; \
             void clear(struct pair* p) { p->n = -1; }";
    let source = "resource counted(c: struct cell*) { field v: int32; owns c->value; fact c->value == v; } \
                  resource pair(p: struct pair*) { owns p->a; owns p->n; owns first: counted(p->a); \
                  fact p->n == first.v; fact first.v >= 0; } \
                  verifying \"f.c\"; void clear(struct pair* p) { owns x: pair(p); } by { \
                  let { first: c } = unfold(x); execute(); let x = fold(pair(p), { first: c }); simp(); }";
    let error = verify_c0_sources(source, &[("f.c", c)]).unwrap_err();
    let report = error.concise_report();
    assert!(report.contains("required body fact: -1 == "), "{report}");
    assert!(!report.contains("first.v == first.v"), "{report}");
}

/// A resource's facts take no label, as a `requires` clause takes none, and
/// the refusal says so rather than reporting a malformed proposition.
#[test]
fn a_labelled_resource_fact_is_refused_by_name() {
    let source = "resource held(p: int32*) { owns *p; fact positive: *p > 0; }";
    let error = verify_c0_sources(source, &[]).unwrap_err();
    assert!(
        error.message.contains("a `fact` clause takes no label"),
        "{}",
        error.message
    );
}

#[test]
fn fold_reports_the_instantiated_body_fact_in_plain_and_matched_resources() {
    let c = "void f(int *p) { *p = 9; }";
    for (resource, proof) in [
        (
            "resource cell(p: int32*) { field value: int32; owns *p; fact *p == value; }",
            "unfold(c); step(); fold(c);",
        ),
        (
            "spec enum Cell { Value(int32) } resource cell(p: int32*) { field model: Cell; match model { Cell::Value(v) => { owns *p; fact *p == v; }, } }",
            "match c.model { Cell::Value(v) => { unfold(c); step(); fold(c); }, }",
        ),
    ] {
        let source = format!(
            "verifying \"f.c\"; {resource} void f(int32* p) {{ owns c: cell(p); }} by {{ {proof} }}"
        );
        let ordinary = verify_c0_sources(&source, &[("f.c", c)]).unwrap_err();
        let report = ordinary.concise_report();
        assert!(report.contains("required body fact"), "{report}");
        assert!(
            report.contains('9') || report.contains("required body fact (declaration):"),
            "{report}"
        );
        assert!(!report.contains("snapshot#"), "{report}");
        let required = report
            .lines()
            .find_map(|line| line.trim().strip_prefix("required body fact: "))
            .unwrap()
            .to_owned();
        with_proof_trace("f", || {
            let error = verify_c0_sources(&source, &[("f.c", c)]).unwrap_err();
            let report = error.trace_context_report().unwrap();
            assert!(report.contains("required body fact"), "{report}");
            assert!(
                report.contains(&format!("required body fact: {required}")),
                "{report}"
            );
            assert!(report.contains('9'), "{report}");
            assert!(
                !report.contains("goal has no exact Click spelling"),
                "{report}"
            );
        });
    }
}

#[test]
fn modular_byte_postcondition_does_not_name_the_whole_scalar() {
    let c_source = r#"
        void fill(unsigned char* p) {
            p[0] = 120;
            p[1] = 86;
            p[2] = 52;
            p[3] = 18;
        }
        unsigned int probe(void) {
            unsigned int obj;
            unsigned char* bytes = (unsigned char*)(void*)&obj;
            fill(bytes);
            return obj;
        }
    "#;
    let click_source = r#"
        verifying "byte_output.c";
        void fill(uint8* p) {
            owns p[0..4];
            ensures p[0] == 120u8;
            ensures p[1] == 86u8;
            ensures p[2] == 52u8;
            ensures p[3] == 18u8;
        } by { execute(); simp(); }
        uint32 probe() {
            ensures result == 305419896u32;
        } by { execute(); simp(); }
    "#;
    with_proof_trace("probe", || {
        let error = verify_c0_sources(click_source, &[("byte_output.c", c_source)])
            .expect_err("ownership and value postconditions alone do not convey initialization");
        assert!(
            error.message().contains("uninitialized"),
            "{}",
            error.message()
        );
        let trace = error.trace_context_report().expect("failure trace");
        // Checked facts retain their snapshot and load kind in the current
        // trace format. Each byte must remain a byte read, never a read of obj.
        assert_eq!(trace.matches("read<UInt8>").count(), 4, "{trace}");
        assert!(trace.contains("pointer=bytes), 120)"), "{trace}");
        assert!(trace.contains(" = bytes + 3 bytes"), "{trace}");
        assert!(trace.contains(", 18) is true"), "{trace}");
        assert!(!trace.contains("pointer=obj)"), "{trace}");
    });
}

#[test]
fn initialized_output_refuses_incomplete_or_redirected_writes() {
    let click_source = r#"
        verifying "output.c";
        void fill(uint8* p) {
            owns p[0..4];
            ensures initialized(p[0..4]);
        } by { execute(); simp(); }
    "#;
    for body in [
        "p[0] = 1; p[1] = 2; p[2] = 3;",
        "p[0] = 1; p[2] = 3; p[3] = 4;",
        "",
        "p = p + 1; p[0] = 2; p[1] = 3; p[2] = 4;",
    ] {
        let c_source = format!("void fill(unsigned char* p) {{ {body} }}");
        let error = match verify_c0_sources(click_source, &[("output.c", &c_source)]) {
            Err(error) => error,
            Ok(_) => panic!("unwritten output accepted: {body}"),
        };
        assert!(
            error.message().contains("initialized(p[0..4])"),
            "{body}: {}",
            error.report()
        );
    }
}

#[test]
fn initialized_output_does_not_grant_write_permission() {
    let c_source = "void fill(unsigned char* p) { p[0] = 1; }";
    let click_source = r#"
        verifying "output.c";
        void fill(uint8* p) { ensures initialized(p[0..1]); }
        by { execute(); simp(); }
    "#;
    let error = verify_c0_sources(click_source, &[("output.c", c_source)])
        .expect_err("initialization guarantees are not write permissions");
    assert!(
        error
            .message()
            .contains("missing resource fact `owns p[0..4]`"),
        "{}",
        error.report()
    );
}

#[test]
fn initialized_output_rejects_unsupported_contract_shapes() {
    let c_source = "void fill(unsigned char* p) { p[0] = 1; }";
    for clause in [
        "requires initialized(p[0..1]); ensures true;",
        "ensures initialized(p[0..1]) && true;",
        "ensures initialized(old(p[0..1]));",
    ] {
        let click_source = format!(
            "verifying \"output.c\"; void fill(uint8* p) {{ owns p[0..1]; {clause} }} by {{ execute(); simp(); }}"
        );
        assert!(
            verify_c0_sources(&click_source, &[("output.c", c_source)]).is_err(),
            "unsupported shape accepted: {clause}"
        );
    }
}

#[test]
fn initialized_output_transfers_without_value_postconditions() {
    let c_source = r#"
        void fill(unsigned char* p) { p[0]=1; p[1]=2; p[2]=3; p[3]=4; }
        unsigned char second(unsigned char* p) { fill(p); return p[1]; }
    "#;
    let click_source = r#"
        verifying "output.c";
        void fill(uint8* p) { owns p[0..4]; ensures initialized(p[0..4]); }
        by { execute(); simp(); }
        uint8 second(uint8* p) { owns p[0..4]; ensures initialized(p[0..4]); ensures result == result; }
        by { execute(); simp(); }
    "#;
    let sources = [("output.c", c_source)];
    verify_c0_sources(click_source, &sources).unwrap();
    let expanded =
        expand_c0_claim_source_by_label(click_source, &sources, "fill.contract").unwrap();
    let expanded = expand_c0_claim_source_by_label(&expanded, &sources, "second.contract").unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
}

#[test]
fn initialized_output_requires_a_defined_read_before_a_write() {
    let c_source = "void fill(unsigned char* p) { p[0] = p[0] + 1; p[1] = 2; p[2] = 3; p[3] = 4; }";
    let click_source = "verifying \"output.c\"; void fill(uint8* p) { owns p[0..4]; ensures initialized(p[0..4]); } by { execute(); simp(); }";
    let error = verify_c0_sources(click_source, &[("output.c", c_source)])
        .expect_err("a promised initialized output does not initialize the input");
    assert!(
        error.message().contains("uninitialized"),
        "{}",
        error.report()
    );
}
/// Unnamed addresses still identify the exact blocking store, using the goal's
/// label map. A history-only diagnostic must not claim missing proof facts.
#[test]
fn memory_history_diagnostic_names_the_store_and_limits_its_claim() {
    use crate::kernel::{LoadKind, intern_c_memory};
    use crate::surface::proof_diagnostics::render::{
        SnapshotLabels, render_memory_history_check, render_proposition_labeled,
    };
    let read = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(992001)),
    };
    let written = Pointer::symbolic(Variable(992002));
    let before = CMemory::new();
    let blocked = before.clone().store(
        written.clone(),
        CValue::UInt64(Bitvector32Term::UInt64Constant(42)),
    );
    let after = blocked.clone().store(
        Pointer {
            block: "local:unrelated".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        int32(1),
    );
    let load = |memory: &CMemory| {
        Bitvector32Term::MemoryLoad(
            intern_c_memory(memory.clone()),
            Box::new(read.clone()),
            LoadKind::Bits64,
        )
    };
    let goal = Proposition::ConditionIs(
        ConditionTerm::Bitvector64Equal(Box::new(load(&after)), Box::new(load(&before))),
        true,
    );
    let summary = super::diagnostics::describe_proposition_version_mismatch(
        &goal,
        &[],
        "earlier",
        ParameterBinding::default(),
    )
    .expect("different snapshots explain the failure");
    assert!(
        summary.contains("without using the proof context's equality and ownership facts"),
        "{summary}"
    );
    assert!(
        summary.contains("subsequent recorded memory transition"),
        "{summary}"
    );
    assert!(!summary.contains("nothing tells"), "{summary}");
    assert!(!summary.contains("later step"), "{summary}");
    let (explanation, _) = super::diagnostics::proposition_version_explanation(
        &goal,
        &[],
        ParameterBinding::default(),
    )
    .unwrap();
    let history = crate::surface::proof_diagnostics::MemoryHistoryDiagnostic::capture(explanation);
    // Clear the live arena before printing, as the terminal renderer may run
    // after the verification session has ended. The retained result must stand.
    let _fresh_session = crate::kernel::VerificationSession::enter();
    let mut labels = SnapshotLabels::default();
    let goal_text = render_proposition_labeled(&goal, &mut labels);
    let report = render_memory_history_check(&history, &mut labels).unwrap();
    let write_name = labels.unnamed_pointer(&written);
    let read_name = labels.unnamed_pointer(&read);
    let stopped = labels.state_phrase(&blocked);
    assert!(report.contains(&format!("stops at {stopped}")), "{report}");
    assert!(
        report.contains(&format!("store: 8 bytes at address `{write_name}`")),
        "{report}"
    );
    assert!(
        report.contains(&format!(
            "read range checked: 16 bytes at address `{read_name}`"
        )),
        "{report}"
    );
    assert!(goal_text.contains(&read_name), "{goal_text}");
    let legend = labels.trace_legend();
    assert!(
        legend.contains(&format!("{stopped} is the memory after a store")),
        "{legend}"
    );
    assert!(!legend.contains("value#"), "{legend}");
}

/// Long checked paths retain their beginning, late target, and added facts.
/// Multiple sizes exercise both former aggregate caps without timing thresholds.
#[test]
#[ignore = "nightly: complete 4096-tactic traces and deterministic lineage scaling take 10s locally"]
fn long_theorem_traces_retain_every_step_and_reach_late_targets() {
    for size in [512, 2048, 4096] {
        let mut source = String::from(
            "theorem long_trace(x: int32) {\n requires x == 0;\n ensures x == 0 by {\n",
        );
        for index in 0..size {
            source.push_str(&format!(
                " have x <= {index} by {{ rewrite(x == 0); normalize(); }}\n"
            ));
        }
        source.push_str(" assumption();\n }\n}\n");
        let project = ClickProject::new(
            "entry.click",
            [ClickModuleSource::new("entry.click", source, [])],
        );
        // Each outer tactic occupies one line; keep source lookup constant-time
        // so this test measures trace retention/rendering, not repeated parsing.
        let locate = |_: &str, path: &[usize]| {
            let line = path[0] + 4;
            Some((format!("tactic@{line}"), SourcePosition::new(line, 1)))
        };
        with_proof_trace("long_trace", || {
            verify_project_theorem(&project, &ProgramInputs::Bundle(Vec::new()), "long_trace")
                .unwrap();
            for target in [None, Some(SourcePosition::new(size + 4, 1))] {
                let trace = accepted_proof_trace(
                    &locate,
                    &|_, _, _| None,
                    &|_, _, _| false,
                    target.as_ref(),
                )
                .unwrap();
                let visits = crate::surface::proof_trace::lineage_visits();
                assert!(
                    visits <= size * 20,
                    "{size} tactics walked {visits} lineage nodes"
                );
                assert_eq!(trace.matches(": have x <= ").count(), size);
                assert!(trace.contains("tactic@4: have x <= 0"));
                assert!(trace.ends_with(&format!("tactic@{}: assumption()", size + 4)));
                assert!(!trace.contains("limit reached"));
                assert!(!trace.contains("no recorded checked step"));
                if size >= 2048 {
                    assert!(trace.len() > 64 * 1024);
                }
            }
        });
    }
}

/// Retargeting changes a resource's index; the next call must show both
/// actual indices and identify the equality it rejected.
#[test]
fn call_resource_diagnostic_shows_the_rejected_argument() {
    let c = r#"void retarget(int32 *p, int32 *q, int32 *anchor) {}
void call(int32 *p, int32 *q, int32 *anchor) { retarget(p, q, anchor); retarget(p, q, anchor); }
"#;
    let source = r#"verifying "call_produced_reuse_requires_new_argument.c";
resource cursor(p: int32*, anchor: int32*) {
    field tag: int32;
    owns *anchor;
}
void retarget(int32* p, int32* q, int32* anchor) {
    consumes a: cursor(p, anchor);
    produces b: cursor(q, anchor);
    ensures b.tag == old(a.tag);
} by {
    unfold(a);
    let b = fold(cursor(q, anchor), { tag: old(a.tag) });
    execute(); simp();
}
void call(int32* p, int32* q, int32* anchor) {
    requires p != q;
    consumes c: cursor(p, anchor);
    produces *anchor;
} by {
    let { b: c } = step(retarget(p, q, anchor), { a: c });
    let { b: d } = step(retarget(p, q, anchor), { a: c });
    unfold(d);
    execute(); simp();
}
"#;
    for tracing in [false, true] {
        let check = || {
            let error = verify_c0_sources(
                source,
                &[("call_produced_reuse_requires_new_argument.c", c)],
            )
            .expect_err("the second call requires the old index");
            let message = error.message();
            assert!(
                message.contains("equality of resource argument 1 was not established"),
                "{message}"
            );
            assert!(message.contains("held:"), "{message}");
            assert!(message.contains("held: owns cursor(q"), "{message}");
            assert!(message.contains("required: owns cursor(p"), "{message}");
        };
        if tracing {
            with_proof_trace("call", check);
        } else {
            check();
        }
    }
}

#[test]
fn call_resource_diagnostic_read_shows_snapshot_and_access() {
    use crate::kernel::{Bitvector32Term, CMemoryRange, Pointer, PointerBlock, PointerOffsetTerm};
    let address = Pointer {
        block: PointerBlock::Concrete("selected_child_cell".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let required = CResourceFact::View(crate::kernel::CResource::Memory(CMemoryRange::new(
        address,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    )));
    let error = crate::kernel::CRuntimeError::ContractResourceDiagnostic {
        reason: "resource `child` argument 1 could not be evaluated: required access authority is unavailable".into(),
        held: None,
        required: Box::new(required),
        memory: Some(Box::new(crate::kernel::CMemory::new())),
    };
    let rendered = super::diagnostics::describe_runtime_error(&error, ParameterBinding::default());
    assert!(
        rendered.contains("arguments read in: function entry"),
        "{rendered}"
    );
    assert!(
        rendered.contains("required: views selected_child_cell[0..1]"),
        "{rendered}"
    );
    assert!(!rendered.contains("snapshot#"), "{rendered}");
}

/// A budget refusal is still a failure at a checked source frontier. The
/// failed search must not discard the preceding accepted store or nested fact.
#[test]
fn smart_have_budget_refusal_retains_checked_trace_prefix() {
    for nested in [false, true] {
        let body = if nested {
            "have value == value by { normalize(); } simp();"
        } else {
            "simp();"
        };
        let source = format!(
            "verifying \"f.c\"; void f(int32 *cell, int32 value) {{ owns cell[0..1]; requires value < 100; ensures cell[0] == value; }} by {{ step(); have cell[0] == value + 1 by {{ {body} }} execute(); simp(); }}"
        );
        with_proof_trace("f", || {
            let error = crate::instrumentation::with_tactic_work_limits(
                crate::instrumentation::TacticWorkLimits {
                    simple: 1_000_000,
                    smart: 128,
                    control: if nested { 128 } else { 1_000_000 },
                },
                || {
                    verify_c0_sources(
                        &source,
                        &[("f.c", "void f(int32 *cell, int32 value) { *cell = value; }")],
                    )
                },
            )
            .expect_err("the bounded false comparison must fail");
            assert!(
                error.message().contains("budget exhausted"),
                "{}",
                error.message()
            );
            let trace = error
                .trace_context_report()
                .expect("the accepted prefix must survive exhaustion");
            assert!(trace.contains("steps through:"), "{trace}");
            assert!(trace.contains("*cell = value"), "{trace}");
            if nested {
                assert!(trace.contains("have value == value"), "{trace}");
            }
            assert!(!trace.contains("adds: cell[0] == value + 1"), "{trace}");
        });
    }
}

#[test]
fn loop_have_budget_refusal_retains_checked_store_trace() {
    let source = r#"verifying "f.c";
        void f(int32 *cell, int32 value) {
            owns cell[0..1]; requires value < 100; ensures cell[0] == value;
        } by {
            step(); step();
            loop {
                invariant i >= 0;
                initialize by { normalize(); }
                preserve by {
                    step();
                    have cell[0] == value + 1 by { simp(); }
                }
            }
            execute(); simp();
        }
    "#;
    with_proof_trace("f", || {
        let error = crate::instrumentation::with_tactic_work_limits(
            crate::instrumentation::TacticWorkLimits {
                simple: 1_000_000, smart: 128, control: 1_000_000,
            },
            || verify_c0_sources(source, &[("f.c", "void f(int32 *cell, int32 value) { int32 i = 1; while (i > 0) { *cell = value; i = i - 1; } }")]),
        ).expect_err("the loop's bounded false comparison must fail");
        assert!(
            error.message().contains("budget exhausted"),
            "{}",
            error.message()
        );
        let trace = error
            .trace_context_report()
            .expect("the loop's checked prefix must survive");
        assert!(trace.contains("steps through: *cell = value"), "{trace}");
        assert!(!trace.contains("adds: cell[0] == value + 1"), "{trace}");
    });
}
