use super::*;

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
            pointers: vec![pointer.clone()],
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

    assert!(
        description.contains("memory mutates only at"),
        "{description}"
    );
    assert!(
        description.contains("memory effect ranges"),
        "{description}"
    );
    assert!(
        description.contains("freed heap allocation"),
        "{description}"
    );
    assert!(!description.contains("CMemory"), "{description}");
    assert!(
        !description.contains("diagnostic truncated"),
        "{description}"
    );
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
                    "comparison fact has no checkable surface form at this proof state",
                ),
            )
        })
        .collect::<Vec<_>>();

    let rendered = super::diagnostics::describe_unexpressed_pure_facts(&failures, &[], &[]);

    assert!(rendered.contains("int32 equality is true"), "{rendered}");
    assert!(rendered.contains("no checkable surface form"), "{rendered}");
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
        error.message().contains("outer wall-clock deadline"),
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
    assert!(message.contains("algebraic value equality"), "{message}");
    assert!(!message.contains("AlgebraicSchemas"), "{message}");
    assert!(!message.contains("AlgebraicTerm"), "{message}");
    assert!(message.len() < 1000, "{message}");
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
    assert!(message.contains("available pure facts: []"), "{message}");
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
    assert_eq!(message.matches("Color::Red").count(), 1, "{message}");
    assert!(!message.contains("missing pure fact"), "{message}");
    assert!(message.len() < 600, "{message}");
}

#[test]
fn negative_mdtest_failures_include_structured_kernel_context() {
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
            assert!(message.contains("owns p[0..1]"), "{name}: {message}");
            assert!(
                message.contains("available resource facts: []"),
                "{name}: {message}"
            );
        } else {
            assert!(message.contains("kernel goal"), "{name}: {message}");
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

int32 pick(struct node* node) {
    requires node != 0;
    views object(node);

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
    assert!(message.len() < 2000, "{message}");
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
