use super::*;
use crate::kernel::binary_node;
use crate::kernel::{CompareRelation, MachineIntegerType};

#[test]
fn full_and_concise_reports_keep_named_pointer_prerequisites() {
    use crate::kernel::{Address, Pointer, ProgramType, Variable};
    use crate::surface::proof_diagnostics::{
        ProofDiagnosticOrigin, ProofDiagnosticState, ProofFailureDiagnostic,
        render::MemoryStateLabels,
    };
    use std::sync::Arc;

    struct NamedPointers {
        node: Address,
        identity: Address,
    }
    impl ProofDiagnosticState for NamedPointers {
        fn kernel_goal(&self) -> Option<&Proposition> {
            None
        }
        fn premises(&self, _: usize) -> Vec<&Proposition> {
            Vec::new()
        }
        fn premise_count(&self) -> usize {
            0
        }
        fn register_names(&self, labels: &mut MemoryStateLabels) {
            labels.immutable_pointer_name(&self.node, "node");
            labels.immutable_pointer_name(&self.identity, "identity");
        }
    }
    let names = NamedPointers {
        node: Address::symbolic(Variable(990_101)),
        identity: Address::symbolic(Variable(990_102)),
    };
    let pointer = |p: &Address| Pointer::new(p.clone(), ProgramType::Int32Pointer);
    let requirement = Proposition::condition_is(
        OldConditionTerm::PointerEqual(
            Box::new(pointer(&names.node)),
            Box::new(pointer(&names.identity)),
        ),
        true,
    );
    let error = ClickError::with_diagnostic(
        "a generated prerequisite has no Surface form",
        ProofFailureDiagnostic {
            failing_path: None,
            checks: None,
            origin: ProofDiagnosticOrigin {
                stage: crate::surface::proof_diagnostics::ProofDiagnosticStage::CheckedStep,
                location: "tactic 4".into(),
                source_tactic_path: None,
            },
            claim_label: "link.contract".into(),
            reason: "a generated prerequisite has no Surface form".into(),
            state: Some(Arc::new(names)),
        },
    )
    .with_unresolved_requirement(&ProofObligation::verification_condition(requirement));
    for report in [error.concise_report(), error.report(), error.report()] {
        assert!(report.contains("goal: node == identity"), "{report}");
        assert!(!report.contains("<pointer"), "{report}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn pointer_cast_goal_keeps_its_written_operands_in_diagnostics() {
    let c = "float* next32(float* p) { return p + 1; }";
    let source = r#"
        verifying "cast.c";
        float* next32(float* p) {
            views p[0..2];
            ensures result == (p as (uint8 *) as (void *) as (float *)) + 1;
            ensures result as (uint8 *) == p as (uint8 *) + 4;
        } by {
            step();
            have result == (p as (uint8 *) as (void *) as (float *)) + 1 by {
                close();
            }
        }
    "#;
    let assert_goal = |report: String| {
        let goal = report
            .lines()
            .find_map(|line| line.trim_start().strip_prefix("goal: "))
            .unwrap_or_else(|| panic!("expected a goal in {report}"));
        assert!(goal.starts_with("result =="), "{report}");
        for cast in ["as (uint8 *)", "as (void *)", "as (float *)"] {
            assert!(goal.contains(cast), "{report}");
        }
    };
    let sources = [("cast.c", c)];
    let error = verify_c_sources(source, &sources).unwrap_err();
    assert_goal(error.concise_report());
    assert_goal(error.report());
    with_proof_trace("next32", || {
        let error = verify_c_sources(source, &sources).unwrap_err();
        assert_goal(error.trace_context_report().unwrap());
    });
}

fn assert_subobject_access_reports(c: &str, source: &str, ordinary_goal: &str, trace_goal: &str) {
    let ordinary = verify_c_sources(source, &[("access.c", c)])
        .unwrap_err()
        .concise_report();
    assert!(ordinary.contains("goal:"), "{ordinary}");
    assert!(ordinary.contains(ordinary_goal), "{ordinary}");
    if ordinary_goal == "subobject bounds of" {
        assert!(ordinary.contains("C address equality alone"), "{ordinary}");
        assert!(!ordinary.contains("have <goal>"), "{ordinary}");
    }
    with_proof_trace("f", || {
        let error = verify_c_sources(source, &[("access.c", c)]).unwrap_err();
        let report = error.trace_context_report().unwrap();
        assert!(!error.raw_summary().contains("resource facts:"), "{report}");
        assert!(report.contains("resources in scope"), "{report}");
        assert!(report.contains("access outside the subobject"), "{report}");
        assert!(report.contains("goal:"), "{report}");
        assert!(report.contains(trace_goal), "{report}");
    });
}

#[test]
fn subobject_access_concrete_bounds_are_reported() {
    assert_subobject_access_reports(
        "struct Pair { int first; int second; }; int f(struct Pair *p) { return *(&p->first + 1); }",
        r#"verifying "access.c"; int32 f(struct Pair *p) {
            views p->first; views p->second; ensures result == p->second;
        }"#,
        "contains(",
        " contains ",
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn subobject_access_opaque_bounds_are_reported() {
    assert_subobject_access_reports(
        "struct node { int tag; struct node *left; }; void f(struct node *p, struct node *g) { struct node *parent = g->left; if (parent == p) { parent->tag = 0; } }",
        r#"verifying "access.c"; void f(struct node *p, struct node *g) { owns *p; owns *g; }"#,
        "subobject bounds of",
        "subobject bounds of",
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn implicit_tail_handles_unsigned_statement_cases_with_tracing() {
    let c = r#"int32 unsigned_index(uint32 x) {
        int32 values[4] = {1, 2, 3, 4};
        int32 r;
        r = 1;
        if (x < 4u) { r = values[x]; }
        return r;
    }"#;
    let source = r#"verifying "unsigned.c";
        int32 unsigned_index(uint32 x) { ensures result == result; }"#;
    let sources = [("unsigned.c", c)];
    verify_c_sources(source, &sources).unwrap();
    with_proof_trace("unsigned_index", || {
        verify_c_sources(source, &sources).unwrap();
    });
    // Explicit index cases discharge this operation without changing the C.
    let explicit = format!(
        "{source} by {{
            step(); step(); step(); step(); step(); step(); step();
            if x < 4u32 {{
                step();
                if x == 0u32 {{ step(); step(); close(); }} else {{
                    if x == 1u32 {{ step(); step(); close(); }} else {{
                        if x == 2u32 {{ step(); step(); close(); }} else {{
                            step(); step(); close();
                        }}
                    }}
                }}
            }} else {{ step(); step(); step(); close(); }}
        }}"
    );
    verify_c_sources(&explicit, &sources).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_00")]
fn unclosed_have_script_retains_its_remaining_goal_and_introduced_premise() {
    let source = r#"verifying "f.c";
        int32 f(int32 x) { ensures result == x; } by {
            have x == 42 implies x == 43 by { intro() {} }
            step_until(function.exit); close();
        }"#;
    with_proof_trace("f", || {
        let error = verify_c_sources(source, &[("f.c", "int f(int x) { return x; }")]).unwrap_err();
        let trace = error.trace_context_report().unwrap();
        assert!(trace.contains("intro"), "{trace}");
        let failed = trace.split("proof refusal:").nth(1).unwrap();
        assert!(failed.contains("proposition proof"), "{trace}");
        assert!(failed.contains("goal: x == 43"), "{trace}");
        assert!(failed.contains("x == 42"), "{trace}");
        assert!(!failed.contains("goal: x == 42 implies"), "{trace}");
    });
    let corrected = source
        .replace("x == 43", "x == 42")
        .replace("intro() {}", "intro() { close(); }");
    verify_c_sources(&corrected, &[("f.c", "int f(int x) { return x; }")]).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_00")]
fn unclosed_theorem_script_retains_its_remaining_goal_and_introduced_premise() {
    let source = r#"theorem unfinished(x: int32) {
        ensures x == 42 implies x == 43 by { intro() {} }
    }"#;
    with_proof_trace("unfinished", || {
        let error = verify_c_sources(source, &[]).unwrap_err();
        let trace = error.trace_context_report().unwrap();
        assert!(trace.contains("intro"), "{trace}");
        let failed = trace.split("proof refusal:").nth(1).unwrap();
        assert!(failed.contains("goal: x == 43"), "{trace}");
        assert!(failed.contains("x == 42"), "{trace}");
        assert!(!failed.contains("goal: x == 42 implies"), "{trace}");
    });
    let corrected = source
        .replace("x == 43", "x == 42")
        .replace("intro() {}", "intro() { close(); }");
    verify_c_sources(&corrected, &[]).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_00")]
fn missing_write_permission_explains_the_available_view_and_failed_check() {
    let c = "void write(int *p) { p[0] = 7; }";
    let source = r#"verifying "write.c"; void write(int32* p) { views p[0..1]; }"#;
    let error = verify_c_sources(source, &[("write.c", c)]).unwrap_err();
    let report = error.concise_report();
    assert!(
        report.contains("missing resource fact `owns p[0]`"),
        "{report}"
    );
    assert!(report.contains("available `views p[0]`"), "{report}");
    assert!(report.contains("permits reading only"), "{report}");
    with_proof_trace("write", || {
        let error = verify_c_sources(source, &[("write.c", c)]).unwrap_err();
        let trace = error.trace_context_report().unwrap();
        assert!(trace.contains("proof refusal:"), "{trace}");
        assert!(trace.contains("resources in scope"), "{trace}");
        assert!(trace.contains("views"), "{trace}");
        assert!(trace.contains("permits reading only"), "{trace}");
        assert!(trace.contains("C operation:"), "{trace}");
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_01")]
fn first_operation_failure_retains_the_required_access_and_empty_resources() {
    let c = "int read(int *p) { return *p; }";
    let source = r#"verifying "read.c"; int32 read(int32* p) { ensures result == 7; }"#;
    with_proof_trace("read", || {
        let error = verify_c_sources(source, &[("read.c", c)]).unwrap_err();
        let trace = error.trace_context_report().unwrap();
        assert!(trace.contains("proof refusal:"), "{trace}");
        assert!(trace.contains("missing resource fact `views"), "{trace}");
        assert!(
            trace.contains("resources in scope (showing 0 of 0)"),
            "{trace}"
        );
        assert!(trace.contains("return *p"), "{trace}");
        // The proof refusal is not presented as an accepted execution step.
        assert!(!trace.contains("steps through:"), "{trace}");
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_01")]
fn execution_tactic_in_a_have_names_the_proposition_context() {
    let c = "int f(void) { return 7; }";
    let source = r#"verifying "f.c"; int32 f() { ensures result == 7; } by { have 1 == 1 by { step_until(function.exit); } step_until(function.exit); close(); }"#;
    let error = verify_c_sources(source, &[("f.c", c)]).unwrap_err();
    let report = error.concise_report();
    assert!(
        report.contains("unsupported proof operation `step_until`"),
        "{report}"
    );
    assert!(report.contains("proposition proof"), "{report}");
    assert!(
        report.contains("C execution cannot advance inside it"),
        "{report}"
    );
    with_proof_trace("f", || {
        let error = verify_c_sources(source, &[("f.c", c)]).unwrap_err();
        let trace = error.trace_context_report().unwrap();
        assert!(trace.contains("proof refusal:"), "{trace}");
        assert!(trace.contains("proof context:"), "{trace}");
        assert!(
            trace.contains("C execution cannot advance inside it"),
            "{trace}"
        );
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_01")]
fn failed_solve_reports_actual_cell_queries_separately_from_history_explanations() {
    let c = "void f(int *p, int i) { p[i] = 9; }";
    let source = r#"verifying "f.c"; void f(int32* p, int32 i) {
        owns p[0..2]; requires 0 <= i; requires i < 2;
        ensures p[0] == old(p[0]);
    }"#;
    with_proof_trace("f", || {
        let error = verify_c_sources(source, &[("f.c", c)]).unwrap_err();
        let trace = error.trace_context_report().unwrap();
        assert!(
            trace.contains("checks observed during the failed attempt"),
            "{trace}"
        );
        assert!(trace.contains("cell walk:"), "{trace}");
        assert!(trace.contains("width: 4 bytes"), "{trace}");
        assert!(
            trace.contains("pointer=p") || trace.contains(" = p"),
            "{trace}"
        );
        assert!(
            trace.contains("step not proved separate") || trace.contains("step affects"),
            "{trace}"
        );
        assert!(trace.contains("queries, not established facts"), "{trace}");
        assert!(
            trace.contains("supplemental history explanation"),
            "{trace}"
        );
        // A supplemental walk is never named as the proof refusal's own.
        assert!(!trace.contains("memory-history check stops at"), "{trace}");
    });
    let separated = source.replace("requires i < 2;", "requires i < 2; requires i == 1;");
    verify_c_sources(&separated, &[("f.c", c)]).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_01")]
fn failed_written_have_keeps_its_goal_and_actual_queries() {
    let c = "void f(int *p, int i) { p[i] = 9; }";
    let source = r#"verifying "f.c"; void f(int32* p, int32 i) {
            owns p[0..2]; requires 0 <= i; requires i < 2;
        } by { step(); have p[0] == old(p[0]) by close(); step_until(function.exit); }"#;
    let ordinary = verify_c_sources(source, &[("f.c", c)])
        .unwrap_err()
        .concise_report();
    assert!(ordinary.contains("premises in scope"), "{ordinary}");
    with_proof_trace("f", || {
        let error = verify_c_sources(source, &[("f.c", c)]).unwrap_err();
        let trace = error.trace_context_report().unwrap();
        assert!(
            trace.contains("checks observed during the failed attempt"),
            "{trace}"
        );
        assert!(trace.contains("premises in scope"), "{trace}");
        assert!(trace.contains("goal:"), "{trace}");
        assert!(trace.contains("cell walk:"), "{trace}");
        assert!(trace.contains("proof refusal:"), "{trace}");
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_02")]
fn failed_outcome_reports_post_call_resources_not_the_execution_entry() {
    let c = "void drop(int *p) {} void f(int *p) { drop(p); }";
    let source = r#"verifying "f.c";
        void drop(int32* p) { consumes p[0..1]; }
        void f(int32* p) { consumes p[0..1]; ensures 1 == 2; }"#;
    with_proof_trace("f", || {
        let error = verify_c_sources(source, &[("f.c", c)]).unwrap_err();
        let trace = error.trace_context_report().unwrap();
        assert!(trace.contains("resource lost: owns"), "{trace}");
        assert!(
            trace.contains("resources in scope (showing 0 of 0)"),
            "{trace}"
        );
        let failed = trace.split("proof refusal:").nth(1).unwrap();
        assert!(!failed.contains("owns memory(p["), "{trace}");
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_02")]
fn callback_sources_keep_field_names_through_subobject_lowering() {
    let functions = syntax::parse_functions_for_source(
        r#"
        struct callbacks {
            void (*propagate)(int32* p);
            void (*copy)(int32* p);
        };
        struct owner { struct callbacks* callbacks; };
        void first(struct callbacks* cb, int32* p) { cb->propagate(p); }
        void later(struct callbacks* cb, int32* p) { cb->copy(p); }
        void nested(struct owner* owner, int32* p) { owner->callbacks->copy(p); }
        "#,
        "callback-names.c",
    )
    .unwrap();
    for (function, expected) in
        functions
            .iter()
            .zip(["cb->propagate", "cb->copy", "owner->callbacks->copy"])
    {
        let sources = function.callback_statement_sources();
        assert_eq!(sources.len(), 1, "{}", function.name());
        let source = sources.values().next().unwrap();
        assert_eq!(
            crate::surface::diagnostics::describe_callback_source(source),
            expected
        );
    }
    assert_eq!(functions.len(), 3);
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_02")]
fn implicit_loop_closure_is_smart() {
    use crate::instrumentation::{VerificationEvent, collect};
    let c = "int f(int n) { while (n > 0) { n = n - 1; } return n; }";
    let source = r#"
        verifying "f.c";
        int32 f(int32 n) { requires n == 2; ensures result == 0; } by {
            loop { invariant n == 2; maintain by { step(); } }
            step_until(function.exit); close();
        }
    "#;
    let (result, events) = collect(|| verify_c_sources(source, &[("f.c", c)]));
    assert!(result.is_err(), "a false invariant must still be rejected");
    assert!(
        events.iter().any(|event| matches!(event,
            VerificationEvent::TacticStarted(tactic)
                if tactic.tactic_name == crate::instrumentation::IMPLICIT_LOOP_CLOSER_TACTIC
                    && tactic.class == "smart" && tactic.source_index == 1
        )),
        "missing smart implicit closer at the owning loop: {events:?}"
    );
    assert!(
        !events.iter().any(|event| matches!(event,
            VerificationEvent::TacticStarted(tactic)
                if tactic.tactic_name == "known" && tactic.class == "simple"
        )),
        "smart planning must not inherit a simple known budget"
    );
}

/// The implicit `solve` proving a bare `fold`'s open body fact is its own
/// smart tactic at the fold's site, so its search is charged to a smart
/// budget and profiled apart from the fold's simple certificate check.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_02")]
fn implicit_solve_is_a_smart_tactic_at_the_simple_tactic_site() {
    use crate::instrumentation::{IMPLICIT_SOLVE_TACTIC, VerificationEvent, collect};
    let source = r#"
        verifying "make.c";
        resource either(n: int32, m: int32) { fact n > 0 or m > 0; }
        void make(int32 x, int32 y) {
            requires x > 0;
            produces either(x, y);
        } by {
            fold(either(x, y));
            step_until(function.exit);
            close();
        }
    "#;
    let (result, events) =
        collect(|| verify_c_sources(source, &[("make.c", "void make(int32 x, int32 y) { }\n")]));
    result.expect("the implicit `solve` proves the fold's open body fact");
    let started = |name: &str| {
        events
            .iter()
            .filter_map(|event| match event {
                VerificationEvent::TacticStarted(tactic) if tactic.tactic_name == name => {
                    Some(tactic.clone())
                }
                _ => None,
            })
            .collect::<Vec<_>>()
    };
    let folds = started("fold");
    let implicit_sites = started(IMPLICIT_SOLVE_TACTIC);
    let [fold] = folds.as_slice() else {
        panic!("one `fold` tactic: {events:?}");
    };
    assert_eq!(fold.class, "simple", "{events:?}");
    assert!(
        !implicit_sites.is_empty(),
        "missing the implicit `solve`: {events:?}"
    );
    for event in &implicit_sites {
        assert_eq!(event.class, "smart", "{events:?}");
        assert_eq!(
            (event.claim.as_str(), event.source_index),
            (fold.claim.as_str(), fold.source_index),
            "the implicit `solve` is profiled at the fold's site: {events:?}"
        );
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_03")]
fn solve_have_budget_failure_keeps_the_exhaustion_reason() {
    let source = r#"
        verifying "bound.c";
        uint64 bound(uint64 a, uint64 b) { ensures result == a; } by {
            have a <= b - b % 4u64;
            step_until(function.exit); close();
        }
    "#;
    let error = crate::instrumentation::with_tactic_work_limits(
        crate::instrumentation::TacticWorkLimits {
            simple: 1_000_000,
            smart: 1,
            control: 1_000_000,
        },
        || {
            verify_c_sources(
                source,
                &[(
                    "bound.c",
                    "unsigned long bound(unsigned long a, unsigned long b) { return a; }",
                )],
            )
        },
    )
    .expect_err("solve must report its exhausted budget");
    assert!(error.message().contains("budget exhausted"), "{error:?}");
    assert!(
        !error.message().contains("`solve` could not prove"),
        "{error:?}"
    );
}

/// A smart closer inside a nested `have` script, `have P by { close(); }`
/// within another `have`'s proof, spends a smart tactic's search: its work
/// is charged to the smart budget and a miss gets the smart advice. It was
/// once charged to the `have`'s control budget and reported as an engine
/// bug.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_03")]
fn smart_closer_inside_a_have_script_spends_the_smart_budget() {
    let source = r#"
        verifying "bound.c";
        uint64 bound(uint64 a, uint64 b) { ensures result == a; } by {
            have a <= b - b % 4u64 by {
                have a <= b - b % 4u64 by { close(); }
                close();
            }
            step_until(function.exit); close();
        }
    "#;
    let error = crate::instrumentation::with_tactic_work_limits(
        crate::instrumentation::TacticWorkLimits {
            simple: 1_000_000,
            smart: 1,
            control: 1_000_000,
        },
        || {
            verify_c_sources(
                source,
                &[(
                    "bound.c",
                    "unsigned long bound(unsigned long a, unsigned long b) { return a; }",
                )],
            )
        },
    )
    .expect_err("the nested solve must exhaust the smart budget");
    assert!(
        error.message().contains(
            "tactic `have` in `bound.contract` exhausted its deterministic smart work budget"
        ),
        "{error:?}"
    );
    assert!(
        error.message().contains("smart search is heuristic"),
        "{error:?}"
    );
}

/// The uint64 bridge creates nested `have` proofs. A missing listed premise
/// must return the arithmetic goal's diagnostic, not panic while wrapping
/// the nested bridge's already-rendered diagnostic inside a new summary.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_03")]
fn wide_arithmetic_unavailable_premise_returns_one_diagnostic() {
    let source = "theorem bound(x: uint64) { requires x <= 100u64; ensures x <= 1000u64 by { close() using { x <= 50u64; } } }";
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

/// A tiny budget stops `close() using` on a wide arithmetic goal before it
/// finishes. Report one bounded diagnostic, with at most one stage, rather
/// than panicking while wrapping the nested refusal.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_03")]
fn wide_arithmetic_budget_refusal_does_not_panic() {
    let source = "theorem bound(x: uint64) { requires x <= 100u64; ensures to_integer(x + 1u64 + 1u64) <= to_integer(1000u64) by { close() using { x <= 100u64; } } }";
    let error = crate::instrumentation::with_tactic_work_limits(
        crate::instrumentation::TacticWorkLimits {
            simple: 1_000,
            smart: 1,
            control: 1,
        },
        || verify_click_theorems(source),
    )
    .expect_err("the constrained bridge must refuse locally");
    assert!(error.raw_summary().contains("budget"), "{error:?}");
    assert!(!error.raw_summary().contains("\n  stage:"));
    assert!(
        error.message().matches("\n  stage:").count() <= 1,
        "{error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_04")]
fn uninitialized_mutex_is_a_named_proof_prerequisite() {
    let c_source = r#"
        #include <pthread.h>
        struct cell { pthread_mutex_t mu; };
        void use_mutex(struct cell *cell) { pthread_mutex_lock(&cell->mu); }
    "#;
    let click_source = r#"
        target "x86_64-unknown-linux-gnu";
        runtime "modeled-pthread";
        verifying "mutex.c";
        void use_mutex(struct cell *cell) { ensures 0 == 0; } by { step(); }
    "#;
    let error = verify_c_sources(click_source, &[("mutex.c", c_source)]).unwrap_err();
    assert_eq!(error.kind(), ClickErrorKind::Proof, "{}", error.message());
    assert!(
        error
            .message()
            .contains("could not prove that mutex `cell` was initialized on this path"),
        "{error:?}"
    );
    assert_eq!(
        error.concise_report_parts().0,
        "tactic error in `use_mutex`:\n  could not prove that mutex `cell` was initialized on this path"
    );
    assert!(!error.message().contains("runtime error"), "{error:?}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_04")]
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
        target "x86_64-unknown-linux-gnu";
        runtime "modeled-pthread";
        resource box_state(box: struct box*) {
            field value: int32;
            owns box->value;
            fact box->value == value;
        }
        verifying "mutex.c";
        void *idle(void *arg) { ensures result == 0; }
        void start(struct box *box) {
            owns box->mu;
            requires aligned(&box->mu, 8);
            owns state: box_state(box);
            ensures 0 == 0;
        } by {
            step();
            step();
            let { lifetime: mutex_lifetime } = step(pthread_mutex_init, { state: state });
            step();
        }
    "#;
    let error = verify_c_sources(click_source, &[("mutex.c", c_source)]).unwrap_err();
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_04")]
fn concise_error_context_preserves_click_binder_colons() {
    assert_eq!(
        concise_error_segments("foo: exists (path: Path) { x: y }: qux"),
        ["foo", "exists (path: Path) { x: y }", "qux"]
    );
    assert_eq!(
        concise_error_segments("foo: `witness(value)`: bar"),
        ["foo", "`witness(value)`", "bar"]
    );
    assert_eq!(
        concise_error_segments("can't close: current goal is exists (path: Path)"),
        ["can't close", "current goal is exists (path: Path)"]
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_04")]
fn concise_reason_keeps_list_entries_and_definitions_whole() {
    assert_eq!(
        concise_reason_lines(
            "`f.contract` tactic 2: transport frame check found no frame evidence\n  \
             source (holds): x == x\n  cell walks:\n    \
             address: value#2; width: 8 bytes; stop: state#3: step not proved separate\n  \
             state#3 = loop effect: may write [p[0..1]]\n  \
             C statement at f.c:6:9: `items[i] = 7;`"
        ),
        [
            (false, "`f.contract` tactic 2"),
            (false, "transport frame check found no frame evidence"),
            (false, "source (holds)"),
            (false, "x == x"),
            (false, "cell walks:"),
            (
                true,
                "address: value#2; width: 8 bytes; stop: state#3: step not proved separate"
            ),
            (false, "state#3 = loop effect: may write [p[0..1]]"),
            (false, "C statement at f.c:6:9"),
            (false, "`items[i] = 7;`"),
        ]
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_05")]
fn click_addition_cancels_a_negated_pointer_base() {
    let base = OldMachineTerm::Variable(Variable(90));
    let index = OldMachineTerm::Variable(Variable(91));
    let negative_base = binary_node!(
        Int32,
        Subtract,
        Box::new(OldMachineTerm::constant(0)),
        Box::new(base.clone()),
    );

    assert_eq!(
        super::lowering::bitvector32_add(
            negative_base,
            binary_node!(Int32, Add, Box::new(base), Box::new(index.clone())),
        ),
        index
    );
}

/// Every external pointer parameter shares one block, so a store to
/// `visited[cur]` can also be spelled through `next`, with the difference of
/// the two bases folded into the index. When the index has no source name —
/// `cur` has since been reassigned, so its store-time value is a term only the
/// lowering names — both spellings read `name[…]`, and the shorter text used
/// to win: a `solve` refusal about `visited[k]` named "the store to `next[…]`".
/// The address belongs to the base its bare index is taken from.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_05")]
fn an_unnamed_store_index_is_spelled_through_its_own_base() {
    use crate::kernel::OffsetTree;
    let base = |variable: u64| {
        Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(variable)), 4),
        )
    };
    let parameters = vec![
        crate::languages::interface::ImportedParameter::new(
            InterfaceType::Int32Pointer,
            "next".to_string(),
            None,
        ),
        crate::languages::interface::ImportedParameter::new(
            InterfaceType::Int32Pointer,
            "visited".to_string(),
            None,
        ),
    ];
    let arguments = vec![
        ProgramExpression::Value(ProgramValue::typed_pointer(
            base(100_000),
            ProgramType::Int32Pointer,
        )),
        ProgramExpression::Value(ProgramValue::typed_pointer(
            base(100_001),
            ProgramType::Int32Pointer,
        )),
    ];
    // `visited + old_cur * 4`, with `old_cur` a variable no local names.
    let store = Address::new(
        AddressBase::ExternalArgument,
        AddressOffset::raw_add(
            base(100_001).offset.clone(),
            AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(1_000_000)), 4),
        ),
    );
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_05")]
fn exact_struct_field_offsets_remain_resolvable_after_deadline() {
    let base = Address::new(
        AddressBase::ExternalArgument,
        AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(100000)), 4),
    );
    let field = base.offset_by_bytes(4);

    let index = crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
        super::checking::pointer_element_index_from_base(&field, &base, &PureFactContext::new())
    });

    assert_eq!(index, Some(OldMachineTerm::constant(1)));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_05")]
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_06")]
fn execution_effect_diagnostics_omit_raw_memory_states() {
    let pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(8));
    let before = SymbolicMemory::new().store(pointer.clone(), int32(1));
    let after = before.clone().store(pointer.clone(), int32(2));
    let facts = vec![
        ExecutionPureFact::new(Proposition::MemoryMutatesOnly {
            before_point: Default::default(),
            after_point: Default::default(),
            before: before.clone(),
            after: after.clone(),
            writes: vec![(pointer.clone(), crate::kernel::AccessExtent::from(4))],
        }),
        ExecutionPureFact::new(Proposition::MemoryEffectSummary {
            before_point: Default::default(),
            after_point: Default::default(),
            before: before.clone(),
            after: after.clone(),
            mutable_ranges: vec![MemoryRange::new(
                pointer.clone(),
                OldMachineTerm::constant(0),
                OldMachineTerm::constant(1),
            )],
        }),
        ExecutionPureFact::new(Proposition::HeapAllocationFreed {
            before_point: Default::default(),
            after_point: Default::default(),
            before,
            after,
            blocks: vec![(
                pointer,
                crate::kernel::AllocationSize::int32(OldMachineTerm::constant(4)),
            )],
            mutable_ranges: Vec::new(),
        }),
    ];

    let description = super::diagnostics::describe_execution_pure_facts(&facts);

    assert!(description.contains("changed between"), "{description}");
    assert!(
        description.contains("written range(s) between"),
        "{description}"
    );
    assert!(description.contains("freed between"), "{description}");
    assert!(!description.contains("SymbolicMemory"), "{description}");
    assert!(
        !description.contains("diagnostic truncated"),
        "{description}"
    );
}

/// A condition search that finds no derivation prints the goal it looked for
/// and the premises it searched, each with its operands in the source's names.
/// It used to read "did not derive signed less-or-equal is true from 2
/// ambient condition facts: [signed less-or-equal is true, ...]", which names
/// neither the goal nor any premise.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_06")]
fn a_condition_search_miss_spells_its_goal_and_premises() {
    let x = OldMachineTerm::Variable(Variable(1));
    let y = OldMachineTerm::Variable(Variable(2));
    let at_most = |term: &OldMachineTerm, bound: u32| {
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: Box::new(term.clone()),
                right: Box::new(OldMachineTerm::constant(bound)),
            },
            true,
        )
    };
    let goal = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left: Box::new(x.clone()),
            right: Box::new(y.clone()),
        },
        true,
    );
    let parameters = vec![
        crate::languages::interface::ImportedParameter::new(
            InterfaceType::Int32,
            "x".to_string(),
            None,
        ),
        crate::languages::interface::ImportedParameter::new(
            InterfaceType::Int32,
            "y".to_string(),
            None,
        ),
    ];
    let arguments = vec![
        ProgramExpression::Value(ProgramValue::Int32(x.clone())),
        ProgramExpression::Value(ProgramValue::Int32(y.clone())),
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_06")]
fn verifier_diagnostics_bound_fact_items() {
    let facts = (0..20)
        .map(|index| {
            Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(OldMachineTerm::constant(index)),
                    right: Box::new(OldMachineTerm::constant(index)),
                },
                true,
            )
        })
        .collect::<Vec<_>>();
    let rendered = super::diagnostics::describe_pure_facts(&facts);
    assert!(rendered.contains("8 more omitted"), "{rendered}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_06")]
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_07")]
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_07")]
fn failed_algebraic_solve_reports_claim_without_internal_schema_dump() {
    let source = r#"
        spec enum Maybe<T> { None, Some(T) }
        theorem false_reconstruction(value: Maybe<int32>) {
            ensures match value {
                Maybe::None => Maybe<int32>::Some(0),
                Maybe::Some(x) => Maybe<int32>::Some(x),
            } == value by close();
        }
    "#;
    let error = verify_c_sources(source, &[]).unwrap_err();
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
/// reachable datatype family for each occurrence of a value, and the `solve`
/// report printed the goal twice.  The bounded printer renders the same claim
/// in its source vocabulary, once.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_07")]
fn failed_compound_algebraic_solve_renders_the_goal_once_without_a_debug_dump() {
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
                close();
            }
        }
    "#;
    let error = verify_c_sources(source, &[]).unwrap_err();
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
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
        let error = verify_c_sources(click, &sources).expect_err(name);
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
                message.contains("left `caller_needs_write_back.owns_0` unproved"),
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
        assert!(!message.contains("SymbolicMemory {"), "{name}: {message}");
    }
}

/// An undecided C `if` reported its two condition paths with the kernel
/// `Debug` of their facts. A condition whose load has not been named by a
/// load variable — the shape `list_count_live` reaches after its recursive
/// call — then carries the whole `SymbolicMemory` state, blocks and heap
/// included, twice. That is the raw-state dump `AGENTS.md` names. Each path
/// is now spelled on its own line in the bounded source vocabulary, which is
/// what says which condition each arm assumes.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_08")]
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
    close();
}
"#;
    let error = verify_c_sources(click_source, &[("pick.c", c_source)]).unwrap_err();
    let message = error.message();
    assert!(
        message.contains("feasible condition paths"),
        "the step should report the undecided C `if`: {message}"
    );
    assert!(
        message.contains("condition path 0:") && message.contains("condition path 1:"),
        "each arm's assumption should be spelled on its own line: {message}"
    );
    assert!(!message.contains("SymbolicMemory {"), "{message}");
    assert!(!message.contains("HeapMemory {"), "{message}");
    assert!(!message.contains("MemoryBlock {"), "{message}");
    assert!(message.len() < 8000, "{message}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_08")]
fn maybe_throwing_step_diagnostic_teaches_outcomes_syntax() {
    let call = crate::kernel::program_call("helper", Vec::new());
    let message =
        super::diagnostics::describe_multiple_statement_successors_guidance(&call, 2, true);

    assert!(
        message.contains("Use `outcomes` at this point"),
        "{message}"
    );
    assert!(message.contains("returned => { }"), "{message}");
    assert!(message.contains("threw => { }"), "{message}");
    assert!(
        message.contains("successor and close its contract claims"),
        "{message}"
    );
}

/// Two successors that both continue are an undecided branch inside an
/// inlined callee. `outcomes` has a `returned` and a `threw` arm and no way to
/// take either of those, so the refusal must not offer it.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_08")]
fn branch_split_step_diagnostic_does_not_offer_outcomes() {
    let call = crate::kernel::program_call("helper", Vec::new());
    let message =
        super::diagnostics::describe_multiple_statement_successors_guidance(&call, 2, false);

    assert!(message.is_empty(), "{message}");
}

/// The one-successor refusal used to print the `While` node with `Debug`,
/// which attaches the body, every lowered invariant and effect check, and
/// every resource spec to the message. A statement head is the statement's own
/// C spelling and nothing else.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_09")]
fn statement_head_names_the_guard_without_the_loop_node() {
    use crate::kernel::{program_assign, program_while};

    let condition = crate::kernel::program_expression::and(
        crate::kernel::program_expression::not_equal(
            crate::kernel::program_expression::variable("a"),
            crate::kernel::program_expression::int32_literal(0),
        ),
        crate::kernel::program_expression::not_equal(
            crate::kernel::program_expression::load(crate::kernel::program_expression::variable(
                "p",
            )),
            crate::kernel::program_expression::int32_literal(0),
        ),
    );
    let body = program_assign(
        "unmistakable_body_local",
        crate::kernel::program_expression::int32_literal(0),
    );
    let loop_statement = program_while(condition, Vec::new(), body);
    let head = super::diagnostics::describe_execution_statement_head(&loop_statement);

    assert_eq!(head, "while ((a != 0) && (*p != 0))");
    assert!(!head.contains("unmistakable_body_local"), "{head}");
    assert!(!head.contains("invariant_checks"), "{head}");

    // A guard spelled past the printer's byte budget is truncated rather than
    // allowed to set the size of the diagnostic.
    let mut wide = crate::kernel::program_expression::not_equal(
        crate::kernel::program_expression::variable("a"),
        crate::kernel::program_expression::int32_literal(0),
    );
    for _ in 0..200 {
        wide = crate::kernel::program_expression::and(
            wide,
            crate::kernel::program_expression::not_equal(
                crate::kernel::program_expression::variable("another_long_operand_name"),
                crate::kernel::program_expression::int32_literal(0),
            ),
        );
    }
    let wide_head = super::diagnostics::describe_execution_statement_head(&program_while(
        wide,
        Vec::new(),
        program_assign("a", crate::kernel::program_expression::int32_literal(0)),
    ));
    assert!(wide_head.len() <= 512, "{}", wide_head.len());
    assert!(wide_head.ends_with('…'), "{wide_head}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_09")]
fn borrow_refusal_diagnostic_renders_only_its_selected_subject() {
    use crate::kernel::{Address, AddressBase, AddressOffset, MemoryRange, OldMachineTerm};
    use crate::kernel::{BorrowRefusal, BorrowRefusalOperation, BorrowRefusalSubject};

    let pointer = Address::new(
        AddressBase::Concrete("selected_resource".to_string()),
        AddressOffset::constant(0),
    );
    let selected = ResourceFact::own_memory(MemoryRange::new(
        pointer,
        OldMachineTerm::constant(0),
        OldMachineTerm::constant(4),
    ));
    let diagnostic = BorrowRefusal::ActiveDependency.diagnostic_with_subject(
        BorrowRefusalOperation::MemoryAccess,
        BorrowRefusalSubject::for_resource(selected),
    );
    let rendered = super::diagnostics::describe_runtime_error(
        &crate::kernel::RuntimeError::BorrowRefusal(Box::new(diagnostic)),
        ParameterBinding::default(),
    );

    assert!(
        rendered.contains("`owns selected_resource[0..4]`"),
        "{rendered}"
    );
    assert!(
        rendered.contains("A live borrow still depends on this resource."),
        "{rendered}"
    );
    assert!(!rendered.contains("unrelated_resource"), "{rendered}");
    assert!(rendered.len() < 1024, "{}", rendered.len());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_09")]
fn borrow_refusal_diagnostic_renders_a_range_subject_without_ledger_state() {
    use crate::kernel::{Address, AddressBase, AddressOffset, MemoryRange, OldMachineTerm};
    use crate::kernel::{BorrowRefusal, BorrowRefusalOperation, BorrowRefusalSubject};

    let range = MemoryRange::new(
        Address::new(
            AddressBase::Concrete("selected_range".to_string()),
            AddressOffset::constant(0),
        ),
        OldMachineTerm::constant(1),
        OldMachineTerm::constant(3),
    );
    let diagnostic = BorrowRefusal::UnsupportedPartition.diagnostic_with_subject(
        BorrowRefusalOperation::Plan,
        BorrowRefusalSubject::for_range(range),
    );
    let rendered = super::diagnostics::describe_runtime_error(
        &crate::kernel::RuntimeError::BorrowRefusal(Box::new(diagnostic)),
        ParameterBinding::default(),
    );

    assert!(rendered.contains("`selected_range[1..3]`"), "{rendered}");
    assert!(
        rendered.contains("The requested ranges must be proved separate."),
        "{rendered}"
    );
    assert!(!rendered.contains("MemoryRange {"), "{rendered}");
    assert!(rendered.len() < 1024, "{}", rendered.len());
}

/// Two distinct loads over the same address used to render identically
/// (`left side evaluated to load(p[0]), right side evaluated to load(p[0])`),
/// which reads as an unprovable `x == x`. The message now reports each side's
/// surface spelling and which state it reads, and appends the checked proof
/// context every other failed goal reports. It does not guess which step was
/// missing.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_09")]
fn identical_load_renders_name_distinct_state_loads() {
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
                ensures result == old(p[0]);
            }
        "#;

    let error = verify_c_sources(click_source, &[("sym_index_clobber.c", c_source)])
        .expect_err("a symbolically-indexed write must leave the old-value goal open");
    let message = error.message();
    assert!(
        message.contains("read the same address in different memory states"),
        "{message}"
    );
    assert!(
        message.contains("`result` reads the memory recorded at `statement(1).exit`"),
        "{message}"
    );
    assert!(
        message.contains("`old(p[0])` reads the function-entry memory"),
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_10")]
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
    use crate::kernel::{OldConditionTerm, OldMachineTerm, Proposition, Variable};
    let i = OldMachineTerm::Variable(Variable(1));
    let j = OldMachineTerm::Variable(Variable(2));
    let differ = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(j.clone()),
            right: Box::new(i.clone()),
        },
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
    let unrelated = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(i.clone()),
            right: Box::new(OldMachineTerm::constant(0)),
        },
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_10")]
fn empty_footprint_rejects_a_fact_aliased_write_and_effect_range() {
    let global = Address::new("global:counter".into(), AddressOffset::constant(0));
    let alias = Address::new(
        AddressBase::Symbolic(Variable(982_001)),
        AddressOffset::constant(0),
    );
    let before = SymbolicMemory::new().with_block(global.base.clone(), 4);
    let pre_state = ExecutionState::new().with_memory(before.clone());
    let aliases_global =
        Proposition::condition_is(OldConditionTerm::address_equal(alias.clone(), global), true);
    let recorded = [
        crate::kernel::RecordedWrites {
            accesses: [(alias.clone(), crate::kernel::AccessExtent::from(4))].into(),
            ..Default::default()
        },
        crate::kernel::RecordedWrites {
            ranges: vec![(
                MemoryRange::new(
                    alias,
                    OldMachineTerm::constant(0),
                    OldMachineTerm::constant(1),
                ),
                crate::kernel::intern_memory(before),
            )],
            ..Default::default()
        },
    ];
    for writes in &recorded {
        crate::kernel::check_empty_contract_write_footprint(
            &pre_state,
            writes,
            &PureFactContext::new(),
        )
        .expect("the symbolic spelling alone does not name preexisting storage");
        let error = crate::kernel::check_empty_contract_write_footprint(
            &pre_state,
            writes,
            &PureFactContext::new().assume_proposition(aliases_global.clone()),
        )
        .expect_err("a fact-aliased write reaches the preexisting global");
        assert!(matches!(
            error,
            crate::kernel::ContractClosingRefusal::Write(_)
                | crate::kernel::ContractClosingRefusal::Range(_)
        ));
    }
}

/// A conditional term's guard is spelled as the comparison it means: a
/// `uint32` order reads as an unsigned comparison of its operands.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_10")]
fn a_conditional_term_spells_its_unsigned_guard() {
    let x = OldMachineTerm::Variable(crate::kernel::Variable(7));
    let term = OldMachineTerm::If {
        condition: Box::new(OldConditionTerm::unsigned_less_than(
            x.clone(),
            OldMachineTerm::constant(4),
        )),
        then_term: Box::new(x),
        else_term: Box::new(OldMachineTerm::constant(5)),
    };
    let rendered = super::diagnostics::describe_bitvector(&term);
    assert!(rendered.contains(" < 4 (unsigned)"), "{rendered}");
    assert!(!rendered.contains('^'), "{rendered}");
}

/// A condition's kind names a `uint32` order as unsigned, as it names a
/// `uint64` one, and never as the signed order of its operands.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_10")]
fn a_uint32_order_is_named_as_unsigned() {
    let (x, y) = (
        OldMachineTerm::Variable(crate::kernel::Variable(8)),
        OldMachineTerm::Variable(crate::kernel::Variable(9)),
    );
    for (condition, kind) in [
        (
            OldConditionTerm::unsigned_less_than(x.clone(), y.clone()),
            "uint32 less-than",
        ),
        (
            OldConditionTerm::unsigned_less_equal(x.clone(), y.clone()),
            "uint32 less-or-equal",
        ),
        (
            OldConditionTerm::unsigned_greater_than(x.clone(), y.clone()),
            "uint32 greater-than",
        ),
        (
            OldConditionTerm::unsigned_greater_equal(x.clone(), y.clone()),
            "uint32 greater-or-equal",
        ),
        (
            OldConditionTerm::uint64_less_than(x.clone(), y.clone()),
            "uint64 less-than",
        ),
    ] {
        assert_eq!(super::diagnostics::condition_kind(&condition), kind);
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_11")]
fn missing_mutex_use_names_the_required_resource_without_borrow_internals() {
    let mutex = Address::new("selected_mutex".into(), AddressOffset::constant(0));
    let rendered = super::diagnostics::describe_runtime_error(
        &crate::kernel::RuntimeError::MissingMutexUse {
            mutex: mutex.clone(),
        },
        ParameterBinding::default(),
    );
    let owner = super::diagnostics::describe_runtime_error(
        &crate::kernel::RuntimeError::MissingMutexLive { mutex },
        ParameterBinding::default(),
    );
    assert_eq!(rendered, owner.replace("mutex_live", "mutex_use"));
    assert!(
        rendered.starts_with("Requires owns mutex_use("),
        "{rendered}"
    );
    assert!(rendered.contains("selected_mutex"), "{rendered}");
    assert!(!rendered.contains("Borrow"), "{rendered}");
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
/// lines and columns, with other comments, parses to equal C and kernel
/// functions and verifies with the same work and the same messages, apart
/// from the `C statement at` line each refusal gains, which names the line
/// and column the statement moved to and quotes it without its comment.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.5s in the parallel gate"]
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
            "int32 store() {\n    ensures result == 0;\n} by {\n    step(); step(); step();\n    loop { decreases 5 - i; invariant i >= 0; invariant i <= 4; }\n    step_until(function.exit); close();\n}\n",
            Some(("f.c:8:9: `items[i].x = 7;`", "f.c:11:11: `items[i].x = 7;`")),
        ),
        (
            "int32 add(int32 a, int32 b) {\n    ensures result == a + b;\n} by {\n    step(); step(); step(); close();\n}\n",
            Some(("f.c:16:5: `total = a + b;`", "f.c:19:7: `total = a + b;`")),
        ),
        (
            "int32 callee(int32 n) {\n    requires n >= 0;\n    ensures result == n;\n}\nint32 caller(int32 n) {\n    ensures result == n + 1;\n} by {\n    step(); step(); step(); close();\n}\n",
            Some((
                "f.c:26:5: `r = callee(n) + 1;`",
                "f.c:29:7: `r = callee(n) + 1;`",
            )),
        ),
        (
            "int32 inc(int32 n) {\n    requires n <= 100;\n    ensures to_integer(result) == to_integer(n + 1);\n} by {\n    step(); close();\n}\n",
            None,
        ),
    ];
    for (proof, expected_sites) in cases {
        let click_source = format!("{header}{proof}");
        // Keep the warm results alive: rejected generated proofs retain
        // shared Integer terms through weak interning, just as successes do.
        // Both measured presentations must start with those terms available.
        let _warm_original = verify_c_sources(&click_source, &[("f.c", SITED_C_SOURCE)]);
        let _warm_moved = verify_c_sources(&click_source, &[("f.c", &shifted)]);
        let (original, original_work) = crate::instrumentation::measure_deterministic_work(|| {
            verify_c_sources(&click_source, &[("f.c", SITED_C_SOURCE)])
        });
        let (moved, moved_work) = crate::instrumentation::measure_deterministic_work(|| {
            verify_c_sources(&click_source, &[("f.c", &shifted)])
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_11")]
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
            step_until(function.exit);
            close();
        }
    "#;
    let error = verify_c_sources(click_source, &[("settle.c", c_source)])
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_11")]
fn a_passing_theorem_retains_its_accepted_trace_path() {
    let source = r#"verifying "f.c";
theorem good(x: int32, y: int32) {
    requires x == y;
    ensures y == x by {
        have y == x by { close(); }
        close();
    }
}
theorem split(x: int32) {
    requires x == 1 or x == 2;
    ensures x >= 1 by {
        cases {
            x == 1 => {
                rewrite(x, 1);
                close();
            }
            x == 2 => {
                rewrite(x, 2);
                close();
            }
        }
    }
}
theorem unproved(x: int32) { ensures x == 0 by { close(); } }
int32 f() { ensures result == 2; } by { step(); close(); }
"#;
    let project = ClickProject::new(
        "entry.click",
        [ClickModuleSource::new("entry.click", source, [])],
    );
    let c = [("f.c", "int f(void) { return 1; }")];
    let index =
        ProofSourceIndex::for_project(&project, &ProgramInputs::Bundle(c.to_vec())).unwrap();
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
            index.nested_position(&outer, &path[1..]).ok()?
        };
        Some((format!("tactic@{}", position.line), position))
    };
    let arm = |claim: &str, path: &[usize], target: &SourcePosition| {
        let (_, branch) = locate(claim, path)?;
        index.arm_containing(&branch, target).ok().flatten()
    };
    with_proof_trace("good", || {
        verify_project_theorem(&project, &ProgramInputs::Bundle(c.to_vec()), "good").unwrap();
        let trace = accepted_proof_trace(&locate, &arm, &|_, _, _| false, None).unwrap();
        assert_eq!(
            trace,
            "proof trace (checked tactics and branch facts):\ntactic@5: have y == x\n  adds: y == x\ntactic@6: close()"
        );
    });
    with_proof_trace("split", || {
        verify_project_theorem(&project, &ProgramInputs::Bundle(c.to_vec()), "split").unwrap();
        let whole = accepted_proof_trace(&locate, &arm, &|_, _, _| false, None).unwrap();
        assert!(whole.ends_with("\ntactic@12: cases (joined)"), "{whole}");
        let right = accepted_proof_trace(
            &locate,
            &arm,
            &|_, _, _| false,
            Some(&SourcePosition::new(19, 17)),
        )
        .unwrap();
        assert!(
            right.ends_with(
                "\ntactic@12: cases (right arm)\n  adds: x == 2\n  tactic@18: rewrite\n  tactic@19: close()"
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn folded_child_loop_field_refusal_names_the_fold_and_a_verified_remedy() {
    let fixture = folded_child_loop_fixture();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let error = verify_c_sources(fixture.click_source.as_deref().unwrap(), &sources).unwrap_err();
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
    verify_c_sources(repaired.click_source.as_deref().unwrap(), &sources)
        .unwrap_or_else(|error| panic!("the suggested payload binding must verify: {error:?}"));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn unfolded_algebraic_field_keeps_its_captured_model() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/loop_invariant_binds_model_from_a_folded_parent.md");
    let fixture =
        crate::cli::parse_mdtest(&path, &std::fs::read_to_string(&path).unwrap()).unwrap();
    let sources = crate::cli::source_refs(&fixture.c_sources);
    let click = fixture.click_source.unwrap();
    let insertion = "        Wrap::Wrap(entry_model) => {";
    assert!(click.contains(insertion));
    let click = click.replacen(
        insertion,
        r#"        Wrap::Wrap(entry_model) => {
            unfold(w);
            have w.model == Wrap::Wrap(entry_model) by { close(); }
            fold(w);"#,
        1,
    );
    verify_c_sources(&click, &sources)
        .unwrap_or_else(|error| panic!("the open parent's captured model must verify: {error:?}"));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_12")]
fn unheld_field_without_a_checked_consumption_does_not_invent_one() {
    let proposition = SyntaxProposition::Comparison {
        operator: ComparisonOperator::Equal,
        left: SyntaxTerm::ResourceField(ResourceFieldAccess {
            owner: "absent".into(),
            resource_name: "cell".into(),
            identity: InstanceId::from_variable(Variable(999)).into(),
            children: vec![],
            field: "rank".into(),
            field_index: 0,
            click_type: Some(ClickType::Program(InterfaceType::Int32)),
        }),
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(crate::kernel::int32(0))),
    };
    let message = crate::surface::diagnostics::describe_consumed_instance_field_read(
        &proposition,
        &ExecutionState::new(),
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_12")]
fn source_unknown_local_pointer_diagnostics_identify_byte_units() {
    use crate::kernel::{
        Address, AddressBase, AddressOffset, MemoryRange, OldMachineTerm, Pointer, ProgramType,
    };
    let base = Address::new(
        AddressBase::Concrete("unknown".into()),
        AddressOffset::constant(0),
    );
    let state = ExecutionState::new().with_local(
        "cursor",
        ProgramValue::Pointer(Pointer::new(base.clone(), ProgramType::Int32Pointer)),
    );
    let (parameters, arguments) = super::diagnostics::local_naming_tables_with_source(&state, None);
    let range = MemoryRange::new(
        base,
        OldMachineTerm::constant(1),
        OldMachineTerm::constant(2),
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
fn address_mismatch_diagnostic_compares_selected_read_points() {
    use crate::kernel::{
        Address, AddressBase, AddressOffset, MemoryRange, ProgramType, ResourceContext,
        ResourceFact, SpecExpression, SpecPoint,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let address = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
    let first = ExecutionState::new()
        .begin_function_entry_memory()
        .with_local(
            "data",
            ProgramValue::typed_pointer(address.clone(), ProgramType::Int32Pointer),
        )
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::view_memory(MemoryRange::new(
                address.clone(),
                OldMachineTerm::constant(0),
                OldMachineTerm::constant(2),
            )),
        ));
    let second = first.clone().begin_function_entry_memory();
    assert_eq!(first.memory(), second.memory());
    assert_ne!(first.observation_point_id(), second.observation_point_id());
    let read = |state: &ExecutionState, bytes| {
        let expression = SpecExpression::MemoryLoad {
            point: SpecPoint::Current,
            pointer: Box::new(SpecExpression::Value(ProgramValue::typed_pointer(
                address.offset_by_bytes(bytes),
                ProgramType::Int32Pointer,
            ))),
            value_type: ProgramType::Int32,
            exact: true,
        };
        crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
            state,
            &expression,
            Some(state),
            &PureFactContext::new(),
        )
        .unwrap()
        .0
    };
    let left = read(&first, 0);
    let right = read(&first, 4);
    let later = read(&second, 4);
    let (parameters, arguments) = super::diagnostics::local_naming_tables_with_source(&first, None);
    let binding = ParameterBinding::new(&parameters, &arguments);
    assert!(super::diagnostics::describe_read_address_mismatch(&left, &right, binding).is_some());
    assert!(super::diagnostics::describe_read_address_mismatch(&left, &later, binding).is_none());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_13")]
fn read_only_wide_index_diagnostic_requests_equality_without_inventing_a_store() {
    let source = "int32 last(int32* data, uint64 length) { return *(data + (length - 1ULL)); }";
    let sidecar = r#"
verifying "last.c";
int32 last(int32* data, uint64 length) {
    owns data[0..1];
    requires length == 1u64;
    ensures result == old(data[0]);
}
"#;
    // Exact wide-index constants now resolve without a manual rewrite.
    verify_c_sources(sidecar, &[("last.c", source)]).unwrap();
    let ambiguous = sidecar
        .replace(
            "owns data[0..1];",
            "owns data[0]; views data[length - 1u64];",
        )
        .replace("requires length == 1u64;", "");
    let error = match verify_c_sources(&ambiguous, &[("last.c", source)]) {
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4.3s in the parallel gate"]
fn callback_script_tails_report_missing_authority_and_complete_valid_steps() {
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
            source = source.replace("step_until(function.exit);", &"step(); ".repeat(10));
        }
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let result = verify_c_sources(&source, &sources);
        if let Some(expected) = expected {
            let error = result.expect_err("missing callback authority must be refused");
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
                report.len() <= 16 * 1024,
                "{fixture_name}: diagnostic is too long"
            );
        } else {
            result.unwrap_or_else(|error| panic!("{fixture_name}: {}", error.message()));
            let named = source.replace(
                &"step(); ".repeat(10),
                "step(); step(); step(Propagate); step(); step(); step(Copy); step(); step(); step(Rotate); step();",
            );
            verify_c_sources(&named, &sources)
                .unwrap_or_else(|error| panic!("named callback steps: {}", error.message()));
            let smart = source.replace(&"step(); ".repeat(10), "step_until(function.exit);");
            let expanded = expand_c_claim_source(
                &smart,
                &sources,
                "erase_augmented",
                ContractProofClaim::Grouped,
            )
            .unwrap();
            verify_c_sources(&expanded, &sources)
                .unwrap_or_else(|error| panic!("expanded callbacks: {}", error.message()));
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn callback_script_tails_complete_or_report_a_bounded_failure() {
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
            // The written steps stop after the first callback; the script's
            // implicit solve tail must finish the remaining valid callbacks.
            (
                source
                    .replace("step_until(function.exit);", "step(); step(); step();")
                    .replace("close();", ""),
                fixture.c_sources,
            )
        } else {
            // Keep a missing Copy fact beyond many valid callbacks. The tail
            // must report that missing authority with a bounded diagnostic.
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
        let result = verify_c_sources(&source, &sources);
        if fixture_name.ends_with("owns.md") {
            let verified =
                result.unwrap_or_else(|error| panic!("{fixture_name}: {}", error.message()));
            assert!(!verified.is_empty());
            // This is the artifact that once made unwrap_err dump pages of
            // proof internals when the script legitimately succeeded.
            for theorem in verified {
                for preview in [format!("{theorem:?}"), format!("{theorem:#?}")] {
                    assert!(
                        preview.len() < 1024,
                        "verified theorem debug output is too long: {} bytes",
                        preview.len()
                    );
                    assert!(preview.contains("erase_augmented"));
                    assert!(!preview.contains("checked_execution"));
                }
            }
        } else {
            let error = result.expect_err("the changed callback must lose its contract authority");
            let report = error.concise_report();
            assert!(
                report.contains("no contract fact for the function pointer `augment->copy`"),
                "{fixture_name}: {report}"
            );
            assert!(
                report.len() <= 16 * 1024,
                "{fixture_name}: diagnostic is too long"
            );
        }
    }
}

/// A member offset that is not a whole struct stride used to be spelled
/// through an unrelated int32 pointer, inventing an anchor/p alias repair.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_13")]
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
            have p[0].left == old(p[0].left) by { close(); }
            step_until(function.exit); close();
        }
    "#;
    let error = verify_c_sources(source, &[("field.c", c_source)])
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_13")]
fn pure_theorem_tactics_emit_claims_and_nested_written_source_paths() {
    use crate::instrumentation::{VerificationEvent, collect};
    let source = r#"theorem nested(x: int32) {
        requires x <= 100;
        ensures x <= 1000 by {
            have x <= 1000 by { close() using { x <= 100; } }
            close();
        }
        ensures x == x by { close(); }
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_13")]
fn pure_theorem_arithmetic_obeys_its_tactic_budget() {
    use crate::instrumentation::{
        TacticWorkLimits, VerificationEvent, collect, with_tactic_work_limits,
    };
    let source = "theorem bound(x: int32) { requires x <= 100; ensures x <= 1000 by { close() using { x <= 100; } } }";
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn wide_conjunction_expansion_stays_parseable_and_checked() {
    let conjuncts: Vec<_> = (1..=40).map(|i| format!("x <= {i}")).collect();
    let source = format!(
        "theorem wide(x: int32) {{ requires x <= 0; ensures {} by {{ close(); }} }}",
        conjuncts.join(" and ")
    );
    verify_click_theorems(&source).unwrap();
    let expanded =
        crate::surface::expand_c_claim_source_by_label(&source, &[], "wide.ensures_0").unwrap();
    verify_click_theorems(&expanded).unwrap();
    assert!(expanded.contains("have "), "{expanded}");
    let invalid = expanded.replacen("requires x <= 0;", "requires x <= 2;", 1);
    assert!(verify_click_theorems(&invalid).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_14")]
fn pure_theorem_generic_and_structural_induction_emit_written_tactics() {
    use crate::instrumentation::{VerificationEvent, collect};
    let source = r#"
    spec enum TestList<T> { Nil, Cons(T, TestList<T>), }
    theorem reflexive<T>(x: T) { ensures x == x by { close(); } }
    theorem induction_shape(xs: TestList<int32>) {
        ensures xs == xs by {
            let ih = induct(xs);
            match xs {
                TestList::Nil => { close(); }
                TestList::Cons(head, tail) => { apply(ih(tail)); close(); }
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
            && tactic.class == "control" && tactic.source_tactic_path.as_deref() == Some(&[1])
    )));
    assert!(events.iter().any(|event| matches!(event,
        VerificationEvent::TacticStarted(tactic) if tactic.claim == "induction_shape.ensures_0"
            && tactic.source_tactic_path.as_deref() == Some(&[1, 1, 0])
    )));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn induction_failure_trace_retains_the_constructor_equation() {
    let source = r#"
        spec enum Chain { End, Next(Chain), }
        function empty(xs: Chain) -> int32 {
            match xs {
                Chain::End => 1,
                Chain::Next(tail) => 0,
            }
        }
        theorem induction_trace(xs: Chain) {
            ensures empty(xs) == 2 by {
                let ih = induct(xs);
                match xs {
                    Chain::End => {
                        unfold(empty(Chain::End));
                        close();
                    },
                    Chain::Next(tail) => {
                        unfold(empty(Chain::Next(tail)));
                        close();
                    },
                }
            }
        }
    "#;
    with_proof_trace("induction_trace", || {
        let error = verify_click_theorems(source).expect_err("the false claim must be refused");
        assert!(error.message().contains("`known` requires"), "{error}");
        let trace = error.trace_context_report().expect("failure trace");
        assert!(trace.contains("adds: xs == Chain::End"), "{trace}");
    });
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: wide uint64 theorem tactic attribution and bounded work"]
fn pure_theorem_wide_arithmetic_has_attributed_work_at_growing_sizes() {
    use crate::instrumentation::{VerificationEvent, collect};
    for size in [8, 16, 32] {
        let expression = format!("x{}", " + 1u64".repeat(size));
        let source = format!(
            "theorem wide(x: uint64) {{ requires x <= 100u64; ensures {expression} <= 1000u64 by {{ close() using {{ x <= 100u64; }} }} }}"
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

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn loop_closer_reuses_published_invariant_facts() {
    let c = "void run(int n, int x) { while (n > 0) { n--; } }";
    let source = r#"verifying "reuse.c";
void run(int32 n, int32 x) { requires n >= 0; requires x == 7; ensures x == 7; } by {
    loop {
        decreases n;
        invariant n >= 0;
        invariant x == 7;
        maintain by {
            step();
            have n >= 0 by { close(); }
            have x == 7 by { close(); }
        }
    }
    step_until(function.exit); close();
}
"#;
    let sources = [("reuse.c", c)];
    let verified = verify_c_sources(source, &sources).unwrap();
    let expanded = expand_checked_function_claim(source, &verified, "run.contract").unwrap();
    verify_c_sources(&expanded, &sources).expect("the retained closure expands and rechecks");
    let invalid = expanded.replace("invariant x == 7;", "invariant x == 8;");
    assert_ne!(invalid, expanded);
    assert!(verify_c_sources(&invalid, &sources).is_err());
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
  maintain by {{ step();  }}
 }}
 step_until(function.exit); close();
}}
"#
    );
    (source.to_owned(), proof)
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 14s whole wide loop expansion and negative recheck"]
fn wide_loop_invariant_bundle_expands_without_dropping_members() {
    // Stay above both the parser limit and the short-bundle cutoff of 24.
    let members = (crate::surface::parser::STRUCTURAL_NESTING_LIMIT + 1).max(25);
    let (source, proof) = wide_loop_invariant_fixture(members);
    let sources = [("bundle.c", source.as_str())];
    let verified_for_label = verify_c_sources(&proof, &sources).unwrap();
    let expanded =
        expand_checked_function_claim(&proof, &verified_for_label, "run.contract").unwrap();
    verify_c_sources(&expanded, &sources).unwrap();
    let last = format!("invariant total <= {};", 1000 + members - 1);
    let invalid = expanded.replacen(&last, "invariant total <= -1;", 1);
    assert_ne!(invalid, expanded);
    assert!(verify_c_sources(&invalid, &sources).is_err());
}

// Default theorem search is measured and bounded without inventing a written
// source occurrence; the CLI declaration-location regression covers failures.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_14")]
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
    assert_eq!(starts[0].tactic_name, "solve");
    assert_eq!(starts[0].source_tactic_path, None);
    assert!(events.iter().any(|event| matches!(event,
        VerificationEvent::ProofClaimFinished { claim, .. } if claim == "implicit.ensures_0"
    )));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_14")]
fn linear_function_proofs_execute_once_at_multiple_sizes() {
    use crate::instrumentation::{VerificationEvent, collect};
    for size in [16, 64, 256] {
        let premises = "have 0 == 0 by { close(); }\n".repeat(size);
        let source = format!(
            "verifying \"f.c\"; int32 f() {{ ensures result == 0; }} by {{ {premises} step_until(function.exit); close(); }}"
        );
        let (result, events) =
            collect(|| verify_c_sources(&source, &[("f.c", "int32 f() { return 0; }")]));
        result.unwrap();
        let executions = events
            .iter()
            .filter(|event| {
                matches!(event,
                    VerificationEvent::TacticStarted(tactic) if tactic.tactic_name == "step_until"
                )
            })
            .count();
        assert_eq!(executions, 1, "linear proof with {size} premises");
    }
}

/// A real child overwrite must report the exact rejected slot and null
/// argument without suggesting that a missing equality is a verifier bug.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_14")]
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
        Tree::Empty => { close(); },
        Tree::Node(id, link, lm, rm) => {
            let { left: l, right: r } = unfold(t);
            mark before_store;
            have p->right == link by { close(); }
            step();
            let t = fold(tree(id), { model: Tree::Node(id, link, lm, rm), left: l, right: r });
            step_until(function.exit); close();
        },
    }
}
"#;
    let ordinary = verify_c_sources(source, &[("f.c", c)]).unwrap_err();
    assert!(
        ordinary
            .message()
            .contains("argument 1 equality is not established")
    );
    assert!(
        ordinary.concise_report().contains("\ngoal: "),
        "{}",
        ordinary.concise_report()
    );
    // The ordinary message spells its facts in source terms, with no
    // kernel state or value labels to define.
    assert!(
        !ordinary.message().contains("state#") && !ordinary.message().contains("value#"),
        "{}",
        ordinary.message()
    );
    with_proof_trace("f", || {
        let error = verify_c_sources(source, &[("f.c", c)]).unwrap_err();
        let report = error.trace_context_report().unwrap();
        assert_eq!(report.matches("\ngoal: ").count(), 1, "{report}");
        assert!(report.contains("child `right`, argument 1"), "{report}");
        assert!(report.contains("supplied: at("), "{report}");
        assert!(report.contains("required: 0"), "{report}");
        assert!(report.contains("at(region(1).entry, p)->right"), "{report}");
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_15")]
fn execute_failure_trace_retains_checked_call_facts() {
    let c = "int helper(void) { return 1; } int f(void) { return helper(); }";
    for execution in ["step_until(function.exit);", "step(); step();"] {
        let source = format!(
            "verifying \"f.c\"; int32 helper() {{ ensures result == 1; }} \
             int32 f() {{ ensures result == 2; }} by {{ {execution} close(); }}"
        );
        with_proof_trace("f", || {
            let error = verify_c_sources(&source, &[("f.c", c)])
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_15")]
fn fold_over_a_hidden_record_names_the_failed_fact() {
    let c = "struct cell { int32 value; }; struct pair { struct cell* a; int32 n; }; \
             void clear(struct pair* p) { p->n = -1; }";
    let source = "resource counted(c: struct cell*) { field v: int32; owns c->value; fact c->value == v; } \
                  resource pair(p: struct pair*) { owns p->a; owns p->n; owns first: counted(p->a); \
                  fact p->n == first.v; fact first.v >= 0; } \
                  verifying \"f.c\"; void clear(struct pair* p) { owns x: pair(p); } by { \
                  let { first: c } = unfold(x); step_until(function.exit); let x = fold(pair(p), { first: c }); close(); }";
    let error = verify_c_sources(source, &[("f.c", c)]).unwrap_err();
    let report = error.concise_report();
    // The instance reads the field the body stored to; the read keeps its
    // name rather than the stored `-1` (`docs/internals/raise-lower-principle.md`).
    assert!(report.contains("goal: p->n == "), "{report}");
    assert!(!report.contains("first.v == first.v"), "{report}");
}

/// A resource's facts take no label, as a `requires` clause takes none, and
/// the refusal says so rather than reporting a malformed proposition.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_15")]
fn a_labelled_resource_fact_is_refused_by_name() {
    let source = "resource held(p: int32*) { owns *p; fact positive: *p > 0; }";
    let error = verify_c_sources(source, &[]).unwrap_err();
    assert!(
        error.message.contains("a `fact` clause takes no label"),
        "{}",
        error.message
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
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
        let ordinary = verify_c_sources(&source, &[("f.c", c)]).unwrap_err();
        let report = ordinary.concise_report();
        // The summary names the declared fact; `goal:` is its instance.
        assert!(report.contains("is not established\n  `*p == "), "{report}");
        let goal = report
            .lines()
            .find_map(|line| line.trim().strip_prefix("goal: "))
            .unwrap_or_else(|| panic!("{report}"));
        // The instance reads the stored cell by name, not the stored `9`.
        assert!(goal.starts_with("p[0] == "), "{report}");
        assert_eq!(report.matches("\ngoal: ").count(), 1, "{report}");
        assert!(!report.contains("state#"), "{report}");
        with_proof_trace("f", || {
            let error = verify_c_sources(&source, &[("f.c", c)]).unwrap_err();
            let report = error.trace_context_report().unwrap();
            let required = report
                .lines()
                .find_map(|line| line.trim().strip_prefix("goal: "))
                .unwrap_or_else(|| panic!("{report}"));
            assert_eq!(report.matches("goal: ").count(), 1, "{report}");
            // The trace states the read, and its label definitions show the
            // store of `9` that read reads.
            assert!(required.contains("read<Bits32>"), "{report}");
            assert!(report.contains("store 9"), "{report}");
            assert!(
                !report.contains("goal has no exact Click spelling"),
                "{report}"
            );
        });
    }
}

#[test]
fn fold_reports_the_selected_missing_body_resource() {
    let source = r#"
        verifying "f.c";
        resource cell(p: int32*) { field value: int32; owns *p; }
        void f(int32* p) { views *p; } by {
            let c = fold(cell(p), { value: 0 });
        }
    "#;
    let files = [("f.c", "void f(int *p) {}")];
    let error = verify_c_sources(source, &files).unwrap_err();
    assert!(error.missing_resource().is_some());
    let report = error.concise_report();
    assert!(report.contains("goal: owns "), "{report}");
    assert!(report.contains("p["), "{report}");
    with_proof_trace("f", || {
        let error = verify_c_sources(source, &files).unwrap_err();
        let trace = error.trace_context_report().unwrap();
        assert!(trace.contains("goal: owns "), "{trace}");
        assert!(trace.contains("p["), "{trace}");
    });
}

/// Unnamed addresses still identify the exact blocking store, using the goal's
/// label map. A history-only diagnostic must not claim missing proof facts.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_16")]
fn memory_history_diagnostic_names_the_store_and_limits_its_claim() {
    use crate::kernel::OffsetTree;
    use crate::kernel::{LoadKind, intern_memory};
    use crate::surface::proof_diagnostics::render::{
        MemoryStateLabels, render_memory_history_check, render_proposition_labeled,
    };
    let read = Address::new(
        AddressBase::ExternalArgument,
        AddressOffset::variable(Variable(992001)),
    );
    let written = Address::symbolic(Variable(992002));
    let before = SymbolicMemory::new();
    let blocked = before.clone().store(
        written.clone(),
        ProgramValue::UInt64(OldMachineTerm::uint64_constant(42)),
    );
    let after = blocked.clone().store(
        Address::new("local:unrelated".into(), AddressOffset::constant(0)),
        int32(1),
    );
    let load = |memory: &SymbolicMemory| {
        OldMachineTerm::read_named(
            crate::kernel::ProgramPoint::at(&(intern_memory(memory.clone()))),
            Box::new(read.clone()),
            LoadKind::Bits64,
        )
    };
    let goal = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(load(&after)),
            right: Box::new(load(&before)),
        },
        true,
    );
    let summary = super::diagnostics::describe_proposition_version_mismatch(
        &goal,
        &[],
        "earlier",
        ParameterBinding::default(),
    )
    .expect("different states explain the failure");
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
    let mut labels = MemoryStateLabels::default();
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
            "read range checked: 8 bytes at address `{read_name}`"
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: complete traces above the former step/text caps and lineage scaling"]
fn long_theorem_traces_retain_every_step_and_reach_late_targets() {
    // Keep a complete path above the former 2048-step and 64-KiB caps.
    // Even the smallest size exceeds the lineage guard's 20x allowance,
    // so walking the full earlier path per step still fails that guard.
    for size in [128, 512, 2049] {
        let mut source = String::from(
            "theorem long_trace(x: int32) {\n requires x == 0;\n ensures x == 0 by {\n",
        );
        for index in 0..size {
            source.push_str(&format!(
                " have x <= {index} by {{ rewrite(x, 0); close(); }}\n"
            ));
        }
        source.push_str(" close();\n }\n}\n");
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
                assert!(trace.ends_with(&format!("tactic@{}: close()", size + 4)));
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
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
    step_until(function.exit); close();
}
void call(int32* p, int32* q, int32* anchor) {
    requires p != q;
    consumes c: cursor(p, anchor);
    produces *anchor;
} by {
    let { b: c } = step(retarget, { a: c });
    let { b: d } = step(retarget, { a: c });
    unfold(d);
    step_until(function.exit); close();
}
"#;
    for tracing in [false, true] {
        let check = || {
            let error = verify_c_sources(
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
            assert!(message.contains("cursor(ptr<int32*>(q)"), "{message}");
            assert!(
                message.contains("required: owns cursor(ptr<int32*>(p)"),
                "{message}"
            );
        };
        if tracing {
            with_proof_trace("call", check);
        } else {
            check();
        }
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_16")]
fn call_resource_diagnostic_read_shows_state_and_access() {
    use crate::kernel::{Address, AddressBase, AddressOffset, MemoryRange, OldMachineTerm};
    let address = Address::new(
        AddressBase::Concrete("selected_child_cell".into()),
        AddressOffset::constant(0),
    );
    let required = ResourceFact::View(crate::kernel::Resource::Memory(MemoryRange::new(
        address,
        OldMachineTerm::constant(0),
        OldMachineTerm::constant(1),
    )));
    let error = crate::kernel::RuntimeError::ContractResourceDiagnostic {
        reason: "resource `child` argument 1 could not be evaluated: required access authority is unavailable".into(),
        held: None,
        required: Box::new(required),
        memory: Some(Box::new(crate::kernel::SymbolicMemory::new())),
    };
    let rendered = super::diagnostics::describe_runtime_error(&error, ParameterBinding::default());
    assert!(
        rendered.contains("arguments read in: function entry"),
        "{rendered}"
    );
    assert!(
        rendered.contains("required: views memory(") && rendered.contains("stride=4"),
        "{rendered}"
    );
    assert!(!rendered.contains("state#"), "{rendered}");
}

/// A budget refusal is still a failure at a checked source frontier. The
/// failed search must not discard the preceding accepted store or nested fact.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_16")]
fn smart_have_budget_refusal_retains_checked_trace_prefix() {
    for nested in [false, true] {
        let body = if nested {
            "have value == value by { close(); } close();"
        } else {
            "close();"
        };
        let source = format!(
            "verifying \"f.c\"; void f(int32 *cell, int32 value) {{ owns cell[0..1]; requires value < 100; requires defined(value * 2); ensures cell[0] == value; }} by {{ step(); have to_integer(cell[0]) < to_integer(value) by {{ {body} }} step_until(function.exit); close(); }}"
        );
        let c = [("f.c", "void f(int32 *cell, int32 value) { *cell = value; }")];
        let (baseline, work) = with_proof_trace("f", || {
            crate::instrumentation::collect_tactic_work(|| verify_c_sources(&source, &c))
        });
        baseline.expect_err("the comparison cannot be proved with the default allowance");
        let have_work = work
            .iter()
            .find(|sample| sample.tactic.tactic_name == "have")
            .expect("the outer have is measured")
            .work;
        with_proof_trace("f", || {
            let error = crate::instrumentation::with_tactic_work_limits(
                crate::instrumentation::TacticWorkLimits {
                    // Exhaust the allowance during the search, after lowering
                    // and any earlier proof steps in the have body.
                    smart: have_work.checked_sub(1).expect("the have consumes work"),
                    ..crate::instrumentation::TacticWorkLimits::default()
                },
                || verify_c_sources(&source, &c),
            )
            .expect_err("the bounded false comparison must fail");
            assert!(
                error.message().contains("budget exhausted"),
                "{}",
                error.message()
            );
            assert_eq!(
                error.proof_refusal(),
                Some(super::ProofRefusal::UnsuccessfulSearch)
            );
            let report = error.concise_report();
            assert!(report.starts_with("unsuccessful search:"), "{report}");
            let trace = error
                .trace_context_report()
                .expect("the accepted prefix must survive exhaustion");
            assert!(trace.contains("steps through:"), "{trace}");
            assert!(trace.contains("*cell = value"), "{trace}");
            if nested {
                assert!(trace.contains("have value == value"), "{trace}");
            }
            assert!(!trace.contains("adds: cell[0] < value"), "{trace}");
            assert!(
                !trace.contains("adds: to_integer(cell[0]) < to_integer(value)"),
                "{trace}"
            );
        });
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_17")]
fn loop_have_budget_refusal_retains_checked_store_trace() {
    let source = r#"verifying "f.c";
        void f(int32 *cell, int32 value) {
            owns cell[0..1]; requires value < 100; ensures cell[0] == value;
        } by {
            step(); step();
            loop {
                invariant i >= 0;
                initialize by { close(); }
                maintain by {
                    step();
                    have cell[0] == value + 1 by { close(); }
                }
            }
            step_until(function.exit); close();
        }
    "#;
    with_proof_trace("f", || {
        let error = crate::instrumentation::with_tactic_work_limits(
            crate::instrumentation::TacticWorkLimits {
                simple: 1_000_000, smart: 128, control: 1_000_000,
            },
            || verify_c_sources(source, &[("f.c", "void f(int32 *cell, int32 value) { int32 i = 1; while (i > 0) { *cell = value; i = i - 1; } }")]),
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

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn loop_certification_refusal_retains_the_loop_frontier_trace() {
    // The `loop` tactic certifies its phases and transitions inside one
    // checked operation. A refusal there, here the loop head's write
    // separation, keeps the proof state at the loop for `--trace-proof`.
    let c = "typedef struct { const unsigned char *content; unsigned long length; unsigned long offset; } buf;\n\
        void skip(buf * const b) {\n\
            while (b->offset < b->length && b->content[b->offset] <= 32) { b->offset++; }\n\
        }\n";
    let source = r#"verifying "f.c";
        void skip(buf * const b) {
            owns b->offset;
            views b->content;
            views b->length;
            let content = b->content;
            let length = b->length;
            requires b != 0;
            requires content != 0;
            requires b->offset <= length;
            views content[0..length];
            ensures b->offset <= length;
        } by {
            step_until(loop(0).entry);
            loop {
                decreases b->length - b->offset;
                invariant b->offset <= b->length;
                maintain by {
                    step();
                    have b->offset <= b->length by { close(); }
                }
            }
        }
    "#;
    with_proof_trace("skip", || {
        let error = verify_c_sources(source, &[("f.c", c)])
            .expect_err("the loop head needs its write separation");
        assert!(
            error.message().contains("loop head write separation"),
            "{}",
            error.message()
        );
        let trace = error
            .trace_context_report()
            .expect("the loop refusal keeps its checked path");
        assert!(trace.contains("proof refusal"), "{trace}");
        assert!(trace.contains("loop head write separation"), "{trace}");
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_17")]
fn ordinary_concise_diagnostics_bound_late_requirement_context() {
    let error = ClickError::new("required fact unavailable")
        .with_missing_tactic_requirement("資源".repeat(DEFAULT_DIAGNOSTIC_BYTE_LIMIT));
    let (summary, context) = error.concise_report_parts();
    assert!(
        summary.len() + context.iter().map(String::len).sum::<usize>()
            > DEFAULT_DIAGNOSTIC_BYTE_LIMIT
    );
    let report = error.concise_report();
    assert!(report.len() <= DEFAULT_DIAGNOSTIC_BYTE_LIMIT);
    assert!(report.starts_with("internal error:"));
    assert!(report.contains("Click did not classify this verifier failure."));
    assert!(report.contains("requirement"));
    assert!(report.contains("diagnostic truncated"));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_17")]
fn ordinary_legacy_diagnostics_bound_late_context_but_traces_remain_full() {
    let error = ClickError::with_diagnostic(
        "required fact unavailable",
        proof_diagnostics::ProofFailureDiagnostic {
            failing_path: None,
            checks: None,
            origin: proof_diagnostics::ProofDiagnosticOrigin {
                stage: crate::surface::proof_diagnostics::ProofDiagnosticStage::Other(
                    "simple checking",
                ),
                location: "資源".repeat(DEFAULT_DIAGNOSTIC_BYTE_LIMIT),
                source_tactic_path: None,
            },
            claim_label: "late_context.ensures_0".into(),
            reason: "required fact unavailable".into(),
            state: None,
        },
    );
    assert!(error.message().len() <= DEFAULT_DIAGNOSTIC_BYTE_LIMIT);
    assert!(error.message().contains("diagnostic truncated"));
    assert!(error.report().len() <= DEFAULT_DIAGNOSTIC_BYTE_LIMIT);
    assert!(error.report().starts_with("required fact unavailable"));
    assert!(error.report().contains("diagnostic truncated"));
    with_proof_trace("late_context", || {
        assert!(error.report().len() > DEFAULT_DIAGNOSTIC_BYTE_LIMIT);
    });
}

const CLOSURE_TRACE_C: &str = r#"unsigned long drain(unsigned long len) {
    while (len >= 16) { len -= 16; }
    return len;
}
"#;

const CLOSURE_TRACE_CLICK: &str = r#"target "x86_64-unknown-linux-gnu";
verifying "loop.c";
uint64 drain(uint64 len) {
 requires len == 16u64;
 ensures result == 0u64;
} by {
 loop {
  decreases to_integer(len);
  invariant len == 0u64 or len == 16u64;
  invariant len == 16u64;
  initialize by { close(); }
  maintain by {
   step();
   have len == 0u64 by close();
   have to_integer(len) == 0 by close() using { len == 0u64; };
  }
 }
 step_until(function.exit); close();
}
"#;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn failed_invariant_closure_retains_body_trace_and_focused_fact() {
    with_proof_trace("drain", || {
        let error = verify_c_sources(CLOSURE_TRACE_CLICK, &[("loop.c", CLOSURE_TRACE_C)])
            .expect_err("the false invariant must be refused at the back edge");
        assert!(
            error.message().contains("remained open"),
            "{}",
            error.message()
        );
        let trace = error.trace_context_report().unwrap();
        assert!(trace.contains("steps through:"), "{trace}");
        assert!(trace.contains("have len == 0u64"), "{trace}");
        assert!(trace.contains("have to_integer(len) == 0"), "{trace}");
        assert!(!trace.contains("no checked simple steps"), "{trace}");
        let project = ClickProject::new(
            "entry.click",
            [ClickModuleSource::new(
                "entry.click",
                CLOSURE_TRACE_CLICK,
                [],
            )],
        );
        let index = ProofSourceIndex::for_project(
            &project,
            &ProgramInputs::Bundle(vec![("loop.c", CLOSURE_TRACE_C)]),
        )
        .unwrap();
        let positions = index
            .project_tactic_positions(&project, error.proof_claim_label().unwrap())
            .unwrap();
        let locate = |path: &[usize]| {
            let outer = positions.get(*path.first()?)?;
            let position = if path.len() == 1 {
                outer.clone()
            } else {
                index.nested_position(outer, &path[1..]).ok()?
            };
            Some((
                format!("tactic@{}:{}", position.line, position.column),
                position,
            ))
        };
        let line = CLOSURE_TRACE_CLICK
            .lines()
            .position(|line| line.contains("have to_integer(len) == 0"))
            .unwrap()
            + 1;
        let target = SourcePosition::new(line, 4);
        let focused = error
            .trace_context_report_with_tactic_locations(
                &locate,
                &|path, target| {
                    index
                        .arm_containing(&locate(path)?.1, target)
                        .ok()
                        .flatten()
                },
                &|path, target| {
                    locate(path).is_some_and(|(_, at)| {
                        index.have_body_contains(&at, target).unwrap_or(false)
                    })
                },
                Some(&target),
            )
            .unwrap();
        assert!(focused.contains("have to_integer(len) == 0"), "{focused}");
        assert!(!focused.contains("no recorded checked step"), "{focused}");
    });
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.6s in the parallel gate"]
fn failed_invariant_closure_trace_prefix_is_lazy_and_scales() {
    for size in [16, 32, 64] {
        let repeated = "   have len == len by close();\n".repeat(size);
        let source = CLOSURE_TRACE_CLICK.replace(
            "   have len == 0u64 by close();\n",
            &format!("{repeated}   have len == 0u64 by close();\n"),
        );
        with_proof_trace("drain", || {
            let error = verify_c_sources(&source, &[("loop.c", CLOSURE_TRACE_C)])
                .expect_err("a trace cannot make the false invariant hold");
            let before = crate::surface::proof_trace::lineage_visits();
            assert!(
                before <= 4 * size + 100,
                "{size} tactics eagerly walked {before} nodes"
            );
            let trace = error.trace_context_report().unwrap();
            let visits = crate::surface::proof_trace::lineage_visits() - before;
            assert!(
                visits <= 8 * size + 200,
                "{size} tactics walked {visits} nodes"
            );
            assert_eq!(trace.matches("have len == len").count(), size, "{trace}");
            assert!(trace.contains("have len == 0u64"), "{trace}");
        });
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_18")]
fn failed_invariant_closure_trace_keeps_its_branch_guard() {
    let c = "unsigned long branch_drain(unsigned long len, int flag) { while (len >= 16) { if (flag == 0) { len -= 16; } else { len -= 8; } } return len; }";
    let source = r#"target "x86_64-unknown-linux-gnu";
        verifying "loop.c";
        uint64 branch_drain(uint64 len, int32 flag) {
            requires len == 16u64;
            ensures result <= 16u64;
        } by {
            loop {
                invariant len == 16u64;
                initialize by close();
                maintain by {
                    if flag == 0 {
                        step();
                        step();
                        have len == 0u64 by close();
                    } else {
                        step();
                        step();
                    }
                }
            }
            step_until(function.exit); close();
        }
    "#;
    with_proof_trace("branch_drain", || {
        let error = verify_c_sources(source, &[("loop.c", c)])
            .expect_err("the deliberately invalid invariant must fail in the then arm");
        let trace = error.trace_context_report().unwrap();
        assert!(trace.contains("flag == 0"), "{trace}");
        assert!(trace.contains("have len == 0u64"), "{trace}");
        assert!(!trace.contains("else arm"), "{trace}");
    });
}

/// Native prefix proofs retain the source view and its coverage bound even
/// when unrelated bounds exceed the general premise-reduction budget.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn native_view_solve_selects_only_coverage_premises() {
    let extra_bounds = 63;
    for body in [
        "close();",
        "have viewable(p[0u64..1u64]) by { close(); } close();",
    ] {
        let mut source = String::from(
            "target \"x86_64-unknown-linux-gnu\"; theorem broad_view(p: uint8[], n: uint64) { views p[0u64..n]; requires 1u64 <= n;",
        );
        for bound in 2..2 + extra_bounds {
            source.push_str(&format!(" requires n <= {bound}u64;"));
        }
        source.push_str(&format!(
            " ensures viewable(p[0u64..1u64]) by {{ {body} }} }}"
        ));
        verify_c_sources(&source, &[])
            .expect("a prefix uses only its source view and coverage bound");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_18")]
fn native_view_solve_distinguishes_a_rejected_kernel_query() {
    let source = "target \"x86_64-unknown-linux-gnu\"; theorem false_view(p: uint8[], n: uint64) { views p[0u64..n]; requires n == 0u64; ensures viewable(p[0u64..1u64]) by { close(); } }";
    let error = verify_c_sources(source, &[]).expect_err("an empty view cannot cover one byte");
    let report = error.concise_report();
    assert!(
        report.contains("kernel native view checker did not establish"),
        "{report}"
    );
    assert!(
        report.contains("solve view derivation selection"),
        "{report}"
    );
    assert!(!report.contains("accepted by the kernel"), "{report}");
    assert!(!report.contains("valid 32-bit byte span"), "{report}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_19")]
fn pending_call_obligations_use_shared_goal_printer_and_state_legend() {
    let _typed = crate::surface::proof_diagnostics::render::TypedNotationScope::enter();
    use crate::kernel::{
        Address, AddressOffset, OldConditionTerm, OldMachineTerm, ProofObligation, Proposition,
        RuntimeError, SymbolicMemory,
    };
    use crate::surface::proof_diagnostics::render::{
        MemoryStateLabels, render_proposition_labeled,
    };
    let memory = SymbolicMemory::new();
    let pointer = Address::new("pending_read_cell".into(), AddressOffset::constant(0));
    let goal = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::read_named(
                crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory(memory))),
                Box::new(pointer),
                crate::kernel::LoadKind::Int32,
            )),
            right: Box::new(OldMachineTerm::constant(7)),
        },
        true,
    );
    let source = std::sync::Arc::new(crate::kernel::CallRequirementSource::new(
        std::sync::Arc::new(crate::kernel::CallRequirementSite::for_requirement(
            "reader",
            "reader.contract",
            0,
            &[],
            &SymbolicMemory::new(),
        )),
        7,
        Some(7),
        false,
        None,
    ));
    let obligations = vec![
        ProofObligation::verification_condition(goal.clone())
            .with_context("child metadata read")
            .with_call_requirement_site(source),
        ProofObligation::verification_condition(goal.clone()).with_context("call postcondition"),
    ];
    let error = RuntimeError::PendingCallObligations(obligations.into());
    let rendered = super::diagnostics::describe_runtime_error(&error, ParameterBinding::default());
    let expected = render_proposition_labeled(
        &goal,
        &mut MemoryStateLabels::naming(ParameterBinding::default()),
    );
    assert_eq!(
        rendered
            .matches(&format!("pending goal: {expected}"))
            .count(),
        2,
        "{rendered}"
    );
    assert!(
        rendered.contains("context: child metadata read"),
        "{rendered}"
    );
    assert!(
        rendered.contains("context: call postcondition"),
        "{rendered}"
    );
    assert_eq!(
        rendered.matches("state#1 = initial empty memory").count(),
        1,
        "{rendered}"
    );
    assert!(
        rendered.contains("callee: reader; source contract input clause 8"),
        "{rendered}"
    );
    assert!(rendered.contains("pending_read_cell"), "{rendered}");
    assert!(!rendered.contains("SymbolicMemory {"), "{rendered}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_19")]
fn function_pointer_load_trace_shows_produced_value_and_read_state() {
    use crate::surface::proof_trace::with_proof_trace;
    let c = r#"
struct callbacks { void (*call)(int *p); };
static void target(int *p) { }
static const struct callbacks table = { .call = target };
void concrete(int *p) {
    const struct callbacks *cb = &table;
    cb->call(p);
}
void symbolic(int *p, const struct callbacks *cb) { cb->call(p); }
"#;
    for (name, contract) in [
        (
            "concrete",
            r#"
void concrete(int32* p) { ensures true; } by {
    step(); step(); step(); step();
    have false by { close(); }
}
"#,
        ),
        (
            "symbolic",
            r#"
void symbolic(int32* p, const struct callbacks* cb) {
    views cb->call;
} by {
    step(); step();
    have false by { close(); }
}
"#,
        ),
    ] {
        let source = format!("verifying \"callbacks.c\";\n{contract}");
        with_proof_trace(name, || {
            let error = verify_c_sources(&source, &[("callbacks.c", c)]).unwrap_err();
            if name == "symbolic" {
                // The call reads its function pointer itself; with no contract
                // for what the pointer holds, the call is refused by the
                // pointer as the source writes it.
                let message = error.message();
                assert!(
                    message.contains("no contract fact for the function pointer `cb->call`"),
                    "{message}"
                );
                return;
            }
            let trace = error
                .trace_context_report()
                .unwrap_or_else(|| panic!("{}", error.concise_report()));
            // The call reads its function pointer itself, and the trace
            // shows the value it read and the state it read it from.
            assert!(trace.contains("step(cb->call(...))"), "{trace}");
            assert!(trace.contains("pointer read at state#"), "{trace}");
            assert!(trace.contains("label definitions"), "{trace}");
            assert!(
                trace.contains(r#"function `"callbacks.c"::target`"#),
                "{trace}"
            );
            assert!(
                trace.contains("\"callbacks.c\"::static(0).storage()"),
                "{trace}"
            );
            assert!(!trace.contains("#file-static"), "{trace}");
        });
    }
}

/// Resource comparisons must not collapse state-dependent pointer arguments
/// to one source address, or replace an unnamed offset with an ellipsis.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_19")]
fn call_resource_diagnostic_distinguishes_exact_pointer_arguments_and_states() {
    use crate::kernel::{
        Address, AddressBase, AddressOffset, AlgebraicValue, LoadKind, Pointer, ProgramType,
        ProgramValue, Resource, SymbolicMemory, Variable, intern_memory,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let read = Address::new(
        AddressBase::Concrete("child_cell".into()),
        AddressOffset::constant(0),
    );
    let before = SymbolicMemory::new();
    let after = before.clone().store(read.clone(), int32(7));
    let argument = |memory: SymbolicMemory| {
        AlgebraicValue::Program(ProgramValue::Pointer(Pointer::new(
            Address::new(
                AddressBase::Concrete("nodes".into()),
                AddressOffset::scale_int32(
                    binary_node!(
                        Int32,
                        Subtract,
                        Box::new(OldMachineTerm::read_named(
                            crate::kernel::ProgramPoint::at(&(intern_memory(memory))),
                            Box::new(read.clone()),
                            LoadKind::Int32,
                        )),
                        Box::new(OldMachineTerm::Variable(Variable(993451))),
                    ),
                    4,
                ),
            ),
            ProgramType::Int32Pointer,
        )))
    };
    let resource = |argument| {
        ResourceFact::own(Resource::Composite {
            name: "optional_size".into(),
            arguments: vec![argument].into(),
        })
    };
    let error = crate::kernel::RuntimeError::ContractResourceDiagnostic {
        reason: "equality of resource argument 1 was not established".into(),
        held: Some(Box::new(resource(argument(before)))),
        required: Box::new(resource(argument(after))),
        memory: None,
    };
    let rendered = super::diagnostics::describe_runtime_error(&error, ParameterBinding::default());
    let held = rendered
        .lines()
        .find(|line| line.contains("held:"))
        .unwrap();
    let required = rendered
        .lines()
        .find(|line| line.contains("required:"))
        .unwrap();
    assert!(held.contains("ptr<int32*>(value#1)"), "{rendered}");
    assert!(required.contains("ptr<int32*>(value#2)"), "{rendered}");
    assert!(
        rendered.contains("state#1") && rendered.contains("state#2"),
        "{rendered}"
    );
    assert!(rendered.contains("read<Bits32>"), "{rendered}");
    assert!(rendered.contains("store"), "{rendered}");
    assert!(!rendered.contains('…'), "{rendered}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_19")]
fn failed_final_known_preserves_its_checked_trace_context() {
    let source = r#"verifying "f.c";
        void f(int32 *cell, int32 value) {
            owns cell[0..1];
            ensures cell[0] == value;
            ensures cell[0] == value + 1;
        } by {
            step(); step();
            have cell[0] == value by { close(); }
            close();
            close();
            close();
        }
    "#;
    with_proof_trace("f", || {
        let error = verify_c_sources(
            source,
            &[("f.c", "void f(int32 *cell, int32 value) { *cell = value; }")],
        )
        .expect_err("the false remaining claim must reject");
        let failed_claim = "`f.ensures_1`";
        assert!(
            error.message().contains(failed_claim),
            "{}",
            error.message()
        );
        assert!(error.concise_report_parts().0.contains(failed_claim));
        let trace = error
            .trace_context_report()
            .expect("retain the failed focused goal's existing context");
        assert!(trace.contains("steps through: *cell = value"), "{trace}");
        assert!(trace.contains("have cell[0] == value"), "{trace}");
        assert!(!trace.contains("adds: cell[0] == value + 1"), "{trace}");
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_20")]
fn known_have_trace_retains_its_written_source_occurrence() {
    let source = r#"verifying "f.c";
        void f(int32 *p) { owns p[0]; requires p[0] == 7; ensures true; } by {
            step(); mark saved;
            have p[0] == 7 by { close(); }
            step_until(function.exit); close();
        }
    "#;
    with_proof_trace("f", || {
        verify_c_sources(
            source,
            &[("f.c", "void f(int32 *p) { int32 y = 0; return; }")],
        )
        .expect("the already known read should close");
        let trace = accepted_proof_trace(&|_, _| None, &|_, _, _| None, &|_, _, _| false, None)
            .expect("the accepted have retains its trace");
        let expected = "have p[0] == 7";
        assert!(trace.contains(&format!("tactic 2: {expected}")), "{trace}");
        let focused = accepted_proof_trace(
            &|_, path| {
                let line = path.first()? + 1;
                Some((format!("tactic@{line}"), SourcePosition::new(line, 1)))
            },
            &|_, _, _| None,
            &|_, _, _| false,
            Some(&SourcePosition::new(3, 1)),
        )
        .expect("the written have source occurrence remains traceable");
        assert!(
            focused.contains(&format!("tactic@3: {expected}")),
            "{focused}"
        );
        assert!(focused.contains("adds: int32 =(read<Bits32>"), "{focused}");
    });
}

/// A step a search produced names the smart tactic or elided form it came
/// from, and an argument the search chose prints as the written form `click
/// expand` gives it. A step the script wrote, or an argument it wrote,
/// prints neither.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_20")]
fn a_trace_marks_searched_steps_and_their_chosen_arguments() {
    let source = r#"verifying "f.c";
        void f(int32 *p) { owns p[0]; requires p[0] == 7; ensures true; } by {
            step(); mark saved;
            have p[0] == 7 by { close(); }
            step_until(function.exit); close();
        }
    "#;
    with_proof_trace("f", || {
        verify_c_sources(
            source,
            &[("f.c", "void f(int32 *p) { int32 y = 0; return; }")],
        )
        .expect("the already known read should close");
        let trace = accepted_proof_trace(&|_, _| None, &|_, _, _| None, &|_, _, _| false, None)
            .expect("the accepted have retains its trace");
        assert!(!trace.contains("chosen: close("), "{trace}");
        assert!(
            trace.contains("tactic 3: step (from `step_until`)"),
            "{trace}"
        );
        assert!(
            trace.contains("have true (from `implicit tail`)"),
            "{trace}"
        );
        assert!(trace.contains("tactic 0: step\n"), "{trace}");
        assert!(trace.contains("tactic 2: have p[0] == 7\n"), "{trace}");
    });
    let source = r#"verifying "f.c";
        theorem le_trans(a: int32, b: int32, c: int32) {
            requires a <= b;
            requires b <= c;
            ensures a <= c;
        }
        theorem use_it(x: int32, y: int32, z: int32) {
            requires x <= y;
            requires y <= z;
            ensures x <= z by { apply(le_trans(x, y, z)); }
        }
    "#;
    with_proof_trace("use_it", || {
        verify_c_sources(source, &[("f.c", "void f(void) { return; }")])
            .expect("the written application checks both premises");
        let trace = accepted_proof_trace(&|_, _| None, &|_, _, _| None, &|_, _, _| false, None)
            .expect("the apply retains its trace");
        assert!(trace.contains("tactic 0: apply\n"), "{trace}");
        assert!(!trace.contains("chosen:"), "{trace}");
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_20")]
fn rejected_historical_fact_retains_store_prefix() {
    let stores = (1..10).map(|i| format!("p[{i}] = 9; ")).collect::<String>();
    let c = format!("void f(int32 *p) {{ {stores} p[0] = 9; return; }}");
    let steps = "step(); ".repeat(9);
    let source = format!(
        r#"verifying "f.c";
        void f(int32 *p) {{ owns p[0..10]; requires p[0] == 7; ensures true; }} by {{
            {steps} mark stored; step();
            have p[0] == 7 by {{ close(); }}
            step_until(function.exit); close();
        }}
    "#
    );
    with_proof_trace("f", || {
        let error = verify_c_sources(&source, &[("f.c", c.as_str())])
            .expect_err("a write invalidates the transported value");
        let report = error.report();
        assert!(
            report.contains("could not establish `p[0] == 7`"),
            "{report}"
        );
        let trace = error
            .trace_context_report()
            .expect("the rejected have retains its checked prefix");
        assert!(trace.contains("read<Bits32>"), "{trace}");
        assert!(trace.contains("steps through: p[1] = 9"), "{trace}");
        assert!(trace.contains("steps through: p[0] = 9"), "{trace}");
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_20")]
fn failed_selected_close_reports_the_wide_read_goal() {
    let c = "void f(uint64 *p) { int32 y = 0; return; }";
    let source = r#"verifying "f.c";
        void f(uint64 *p) { owns p[0]; ensures true; } by {
            step();
            have p[0] == 7u64 by { close() using {}; };
            step_until(function.exit); close();
        }
    "#;
    with_proof_trace("f", || {
        let error = verify_c_sources(source, &[("f.c", c)])
            .expect_err("an unknown initial word need not be seven");
        let trace = error
            .trace_context_report()
            .expect("the failed written check retains its diagnostic state");
        for expected in [
            "could not prove the current goal from only its listed premises",
            "read<Bits64>",
            "no instrumented memory query was recorded",
        ] {
            assert!(trace.contains(expected), "missing {expected}: {trace}");
        }
        assert!(trace.contains("steps through: declare y"), "{trace}");
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_21")]
fn rejected_wide_historical_fact_retains_store_prefix() {
    let c = "void f(uint64 *p) { p[0] = 9; int32 y = 0; return; }";
    let source = r#"verifying "f.c";
        void f(uint64 *p) {
            owns p[0]; requires p[0] == 7u64; ensures true;
        } by {
            mark before_write; step();
            have p[0] == 7u64 by { close(); }
            step_until(function.exit); close();
        }
    "#;
    with_proof_trace("f", || {
        let error = verify_c_sources(source, &[("f.c", c)])
            .expect_err("a real write invalidates the old word");
        let report = error.report();
        assert!(
            report.contains("could not establish `p[0] == 7u64`"),
            "{report}"
        );
        let trace = error
            .trace_context_report()
            .expect("retain the failed written check's prefix");
        assert!(trace.contains("read<Bits64>"), "{trace}");
        assert!(trace.contains("steps through: p[0] = 9"), "{trace}");
    });
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/surface/tests/diagnostic_tests.rs");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: repeated-retain source diagnostic took 0.63s in parallel"]
fn a_failed_retain_names_the_population_count_requirement() {
    for (name, call_line) in [
        (
            "repeated_child_retains_require_enough_count_capacity.md",
            11,
        ),
        ("repeated_child_retains_grown_count_requirement.md", 12),
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(name);
        let markdown = std::fs::read_to_string(&path).unwrap();
        let fixture = crate::cli::parse_mdtest(&path, &markdown).unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let error = verify_c_sources(fixture.click_source.as_deref().unwrap(), &sources)
            .expect_err("the caller does not establish the helper's stricter count bound");
        let (report, _) = error.concise_report_parts();
        assert!(
            report.contains("precondition clause 1 of `child_retain`"),
            "{report}"
        );
        // Both obligations name the current count. The second fixture must
        // accept the first call and reject the next one after count growth.
        assert!(
            report.contains("to_integer(count(child_ref(obj))) < 8"),
            "{report}"
        );
        assert!(
            report.contains(&format!("C statement at retain.c:{call_line}:5")),
            "{report}"
        );
        assert!(!report.contains("*obj"), "{report}");
    }
}

/// A `have` miss keeps the same checked prefix as other have failures.
/// The failed smart candidates must not become facts in that prefix.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_21")]
fn have_failure_trace_retains_checked_call_prefix() {
    let c = "int helper(void) { return 1; } int f(void) { int x; x = helper(); return x; }";
    let source = "verifying \"f.c\"; int32 helper() { ensures result == 1; } \
                  int32 f() { ensures result == 1; } by { step(); step(); step(); have x == 2; step_until(function.exit); close(); }";
    with_proof_trace("f", || {
        let error =
            verify_c_sources(source, &[("f.c", c)]).expect_err("the false have must still fail");
        assert!(error.raw_summary().contains("could not establish `x == 2`"));
        assert_eq!(error.proof_claim_label(), Some("f.contract"));
        let trace = error.trace_context_report().expect("checked prefix trace");
        assert!(trace.contains("step(helper("), "{trace}");
        assert!(
            trace.contains("== 1") || trace.contains(", 1) is true"),
            "{trace}"
        );
        assert!(!trace.contains("adds: x == 2"), "{trace}");
        assert!(!trace.contains("<no checked simple steps"), "{trace}");
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_21")]
fn budget_stopped_close_retains_its_checked_loop_prefix() {
    use crate::instrumentation::{TacticWorkLimits, with_tactic_work_limits};
    let source = r#"verifying "f.c";
        void f(int32 *p) { owns p[0]; requires p[0] == 7; ensures true; } by {
            loop {
                owns p[0];
                invariant p[0] == 7;
                decreases 0;
                initialize by { close(); }
                maintain by {
                    mark before;
                    step();
                    have p[0] == 7 by { close(); }
                    step();
                }
            }
            step_until(function.exit); close();
        }
    "#;
    with_proof_trace("f", || {
        let error = with_tactic_work_limits(
            TacticWorkLimits {
                smart: 0,
                ..TacticWorkLimits::default()
            },
            || {
                verify_c_sources(
                    source,
                    &[("f.c", "void f(int32 *p) { while (1) { *p = 9; break; } }")],
                )
            },
        )
        .expect_err("the written close has no work allowance");
        assert!(error.message().contains("budget"), "{}", error.message());
        let trace = error
            .trace_context_report()
            .expect("attach the checked predecessor even on a budget error");
        assert!(trace.contains("steps through: *p = 9"), "{trace}");
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_22")]
fn callback_refinement_hint_with_produced_resource_is_a_checked_proof() {
    let source = r#"verifying "callback.c";
        spec enum Ref { At(struct node*), }
        resource token() { field model: Ref; }
        contract void Callback(struct node* p) {
            produces held: token(); ensures held.model == Ref::At(p);
        }
        void wrapped(struct node* p) {
            produces held: token(); ensures held.model == Ref::At(p);
        } by { step_until(function.exit); let held = fold(token(), { model: Ref::At(p) }); }
        /* REFINEMENT */
        int32 accept(void (*f)(struct node*)) {
            requires Callback(f); ensures result == 0;
        } by { step_until(function.exit); close(); }
        int32 caller() { ensures result == 0; } by { /* APPLY */ step_until(function.exit); }
    "#;
    let c = [(
        "callback.c",
        "struct node { uint64 word; }; void wrapped(struct node* p) {} int32 accept(void (*f)(struct node*)) { return 0; } int32 caller() { return accept(&wrapped); }",
    )];
    let error = verify_c_sources(source, &c).unwrap_err();
    let report = error.concise_report();
    let suggestion = report
        .split_once("prove it explicitly:\n")
        .expect(&report)
        .1;
    let start = suggestion.find("theorem ").expect(&report);
    let mut depth = 0;
    let end = suggestion[start..]
        .char_indices()
        .find_map(|(offset, character)| {
            match character {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(offset + 1);
                    }
                }
                _ => {}
            }
            None
        })
        .expect(&report);
    let theorem = &suggestion[start..start + end];
    let corrected = source
        .replace("/* REFINEMENT */", theorem)
        .replace("/* APPLY */", "apply(wrapped_is_callback());");
    verify_c_sources(&corrected, &c).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_22")]
fn failed_branch_interface_retains_its_arm_and_written_requirement() {
    let c = "int advance(int x) { int y; if (x >= 0) { y = x; } else { y = 0; } return y; }";
    for (requirement, precondition, chosen, other) in [
        ("y == 0", "", "then", "else"),
        ("y == x", "", "else", "then"),
        ("y == 0", "requires x >= 0;", "then", "else"),
    ] {
        let source = format!(
            r#"verifying "branch.c";
            int32 advance(int32 x) {{
                {precondition}
                ensures result == result by {{
                    step();
                    branch ensuring {{ fact {requirement}; }} {{ true => {{ step(); }} false => {{ step(); }} }}
                    step(); close();
                }}
            }}
        "#
        );
        with_proof_trace("advance", || {
            let error = verify_c_sources(&source, &[("branch.c", c)])
                .expect_err("the chosen arm does not establish the interface");
            assert!(
                error.message().contains("did not establish fact"),
                "{error}"
            );
            let trace = error
                .trace_context_report()
                .expect("the rejected interface must retain the checked arm");
            assert!(trace.contains(&format!("{chosen} arm")), "{trace}");
            assert!(!trace.contains(&format!("{other} arm")), "{trace}");
            let written = error
                .unresolved_requirement()
                .and_then(|requirement| requirement.surface.as_ref())
                .expect("the interface failure must retain its written requirement");
            assert_eq!(
                crate::surface::printing::source_click_proposition(written),
                requirement
            );
            assert!(error.message().contains(requirement), "{error}");
        });
    }
}

/// Rule K6: a `uint32` equality is filed at `uint32`, so a refusal that
/// lists it prints its constant in its own type, `4294967295u32`, not as the
/// `int32` reading `-1`.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_22")]
fn a_uint32_equality_above_int32_max_prints_in_its_own_type() {
    let source = "verifying \"t.c\";\nunsigned read(unsigned *u) {\n    requires u[0] == 4294967295u32;\n    ensures result == 4294967295u32;\n}\n";
    let error = verify_c_sources(
        source,
        &[("t.c", "unsigned read(unsigned *u) { return *u; }")],
    )
    .unwrap_err();
    let message = error.message();
    assert!(message.contains("old(u[0]) == 4294967295u32"), "{message}");
    assert!(!message.contains("== -1"), "{message}");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn resource_separation_matches_written_goal_with_pointer_alias() {
    let c = r#"struct callbacks { void (*call)(int *p); };
        static void target(int *p) { }
        static const struct callbacks table = { .call = target };
        void copy(const struct callbacks *cb, struct callbacks *out) { out->call = cb->call; }"#;
    let source = r#"verifying "callback-read.c";
        void copy(const struct callbacks* cb, struct callbacks* out) {
            requires cb == &table;
            views cb->call;
            owns out->call;
        } by {
            have separate(memory(out->call), memory(cb->call)) by close();
        }"#;
    // Resource admission and the written goal must retain the same pointer
    // carrier, even when a precondition equates its address to a global object.
    verify_c_sources(source, &[("callback-read.c", c)]).unwrap();
    let no_alias = source.replace("requires cb == &table;", "");
    verify_c_sources(&no_alias, &[("callback-read.c", c)]).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_23")]
fn struct_pointer_pointer_ranges_print_pointer_units() {
    let function = crate::languages::c::syntax::parse_function(
        "struct item { uint8 tag; int64 value; }; void inspect(struct item **pp) {}",
    )
    .unwrap();
    let pointer = crate::kernel::Pointer::new(
        Address::new(
            AddressBase::Concrete("array".into()),
            AddressOffset::constant(0),
        ),
        ProgramType::Int32PointerPointer,
    );
    let arguments = [ProgramExpression::Value(ProgramValue::Pointer(
        pointer.clone(),
    ))];
    for (start, end) in [(0, 4), (1, 3)] {
        let range = MemoryRange::from_pointer_value(
            &pointer,
            OldMachineTerm::constant(start),
            OldMachineTerm::constant(end),
            8,
        );
        assert_eq!(
            super::diagnostics::describe_memory_range(
                &range,
                ParameterBinding::new(function.parameters(), &arguments)
            ),
            format!("pp[{start}..{end}]"),
        );
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_23")]
fn failed_invariant_after_branch_join_reports_the_join() {
    for (then_arm, else_arm) in [("len -= 16;", "len = 16;"), ("len = 16;", "len -= 16;")] {
        let c = format!(
            "unsigned long branch_drain(unsigned long len, int flag) {{ while (len >= 16) {{ if (flag == 0) {{ {then_arm} }} else {{ {else_arm} }} }} return len; }}"
        );
        let source = r#"target "x86_64-unknown-linux-gnu";
            verifying "loop.c";
            uint64 branch_drain(uint64 len, int32 flag) {
                requires len == 16u64;
                ensures result <= 16u64;
            } by {
                loop {
                    invariant len == 16u64;
                    initialize by close();
                    maintain by { branch { true => { step(); } false => { step(); } } }
                }
                step_until(function.exit); close();
            }
        "#;
        with_proof_trace("branch_drain", || {
            let error = verify_c_sources(source, &[("loop.c", c.as_str())])
                .expect_err("one arm violates the invariant");
            let trace = error.trace_context_report().unwrap();
            assert_eq!(
                error.proof_source_tactic_path(),
                Some(&[2][..]),
                "{}",
                error.report()
            );
            assert!(trace.contains("branch (joined)"), "{trace}");
            assert!(!trace.contains("else arm"), "{trace}");
            assert!(
                error.message().contains("after the `branch` join"),
                "{}",
                error.report()
            );
            assert!(
                error.message().contains("branch ensuring"),
                "{}",
                error.report()
            );
        });
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_23")]
fn failed_postcondition_after_branch_join_keeps_the_join_trace() {
    let c = "unsigned long choose(int flag) { unsigned long len; if (flag == 0) { len = 0; } else { len = 16; } return len; }";
    let source = r#"target "x86_64-unknown-linux-gnu";
        verifying "choose.c";
        uint64 choose(int32 flag) {
            ensures result == 16u64;
        } by {
            step();
            branch { true => { step(); } false => { step(); } }
            step();
        }
    "#;
    with_proof_trace("choose", || {
        let error = verify_c_sources(source, &[("choose.c", c)])
            .expect_err("the joined return does not establish the postcondition");
        let trace = error.trace_context_report().unwrap();
        assert!(trace.contains("branch (joined)"), "{trace}");
        assert!(!trace.contains("else arm"), "{trace}");
        assert_ne!(
            error.proof_source_tactic_path(),
            Some(&[3][..]),
            "{}",
            error.report()
        );
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_24")]
fn child_argument_goal_reports_scalar_indices() {
    let source = r#"
verifying "f.c";
resource cell(p: int32*, index: int32) { field value: int32; owns *p; }
resource holder(p: int32*) { field value: int32; owns child: cell(p, 1); fact child.value == value; }
void f(int32* p) { consumes c: cell(p, 0); ensures true; } by {
    let h = fold(holder(p), { value: c.value, child: c });
}
"#;
    let c = "void f(int *p) {}";
    let ordinary = verify_c_sources(source, &[("f.c", c)]).unwrap_err();
    let report = ordinary.concise_report();
    assert!(
        report.contains("argument 2 equality is not established"),
        "{report}"
    );
    assert!(report.contains("goal: 0 == 1"), "{report}");
    with_proof_trace("f", || {
        let error = verify_c_sources(source, &[("f.c", c)]).unwrap_err();
        let report = error.trace_context_report().unwrap();
        assert_eq!(report.matches("\ngoal: ").count(), 1, "{report}");
        assert!(report.contains("goal: 0 == 1"), "{report}");
    });
}

#[cfg(feature = "fast-gate")]
test_batches! {
    file: "diagnostic_tests.rs",
    marker: "diagnostic_batch_",
    diagnostic_batch_00: [
        unclosed_have_script_retains_its_remaining_goal_and_introduced_premise,
        unclosed_theorem_script_retains_its_remaining_goal_and_introduced_premise,
        missing_write_permission_explains_the_available_view_and_failed_check,
    ],
    diagnostic_batch_01: [
        first_operation_failure_retains_the_required_access_and_empty_resources,
        execution_tactic_in_a_have_names_the_proposition_context,
        failed_solve_reports_actual_cell_queries_separately_from_history_explanations,
        failed_written_have_keeps_its_goal_and_actual_queries,
    ],
    diagnostic_batch_02: [
        failed_outcome_reports_post_call_resources_not_the_execution_entry,
        callback_sources_keep_field_names_through_subobject_lowering,
        implicit_loop_closure_is_smart,
        implicit_solve_is_a_smart_tactic_at_the_simple_tactic_site,
    ],
    diagnostic_batch_03: [
        solve_have_budget_failure_keeps_the_exhaustion_reason,
        smart_closer_inside_a_have_script_spends_the_smart_budget,
        wide_arithmetic_unavailable_premise_returns_one_diagnostic,
        wide_arithmetic_budget_refusal_does_not_panic,
    ],
    diagnostic_batch_04: [
        uninitialized_mutex_is_a_named_proof_prerequisite,
        worker_without_protocol_contract_is_a_proof_error,
        concise_error_context_preserves_click_binder_colons,
        concise_reason_keeps_list_entries_and_definitions_whole,
    ],
    diagnostic_batch_05: [
        click_addition_cancels_a_negated_pointer_base,
        an_unnamed_store_index_is_spelled_through_its_own_base,
        exact_struct_field_offsets_remain_resolvable_after_deadline,
        verifier_diagnostics_are_bounded_deterministically_at_utf8_boundaries,
    ],
    diagnostic_batch_06: [
        execution_effect_diagnostics_omit_raw_memory_states,
        a_condition_search_miss_spells_its_goal_and_premises,
        verifier_diagnostics_bound_fact_items,
        expired_project_deadline_outweighs_semantic_mismatch_diagnostic,
    ],
    diagnostic_batch_07: [
        exhausted_work_budget_outweighs_missing_path_goal_diagnostic,
        failed_algebraic_solve_reports_claim_without_internal_schema_dump,
        failed_compound_algebraic_solve_renders_the_goal_once_without_a_debug_dump,
    ],
    diagnostic_batch_08: [
        undecided_c_branch_step_reports_its_paths_without_a_memory_dump,
        maybe_throwing_step_diagnostic_teaches_outcomes_syntax,
        branch_split_step_diagnostic_does_not_offer_outcomes,
    ],
    diagnostic_batch_09: [
        statement_head_names_the_guard_without_the_loop_node,
        borrow_refusal_diagnostic_renders_only_its_selected_subject,
        borrow_refusal_diagnostic_renders_a_range_subject_without_ledger_state,
        identical_load_renders_name_distinct_state_loads,
    ],
    diagnostic_batch_10: [
        a_store_wider_than_an_element_is_refused_by_bytes_not_by_index,
        empty_footprint_rejects_a_fact_aliased_write_and_effect_range,
        a_conditional_term_spells_its_unsigned_guard,
        a_uint32_order_is_named_as_unsigned,
    ],
    diagnostic_batch_11: [
        missing_mutex_use_names_the_required_resource_without_borrow_internals,
        failed_generated_loop_closer_reports_a_short_summary_at_the_loop_tactic,
        a_passing_theorem_retains_its_accepted_trace_path,
    ],
    diagnostic_batch_12: [
        unheld_field_without_a_checked_consumption_does_not_invent_one,
        source_unknown_local_pointer_diagnostics_identify_byte_units,
    ],
    diagnostic_batch_13: [
        read_only_wide_index_diagnostic_requests_equality_without_inventing_a_store,
        struct_field_frame_failure_names_the_read_and_written_members,
        pure_theorem_tactics_emit_claims_and_nested_written_source_paths,
        pure_theorem_arithmetic_obeys_its_tactic_budget,
    ],
    diagnostic_batch_14: [
        pure_theorem_generic_and_structural_induction_emit_written_tactics,
        implicit_theorem_search_is_timed_without_a_written_tactic_path,
        linear_function_proofs_execute_once_at_multiple_sizes,
        child_argument_trace_reports_the_rejected_pair,
    ],
    diagnostic_batch_15: [
        execute_failure_trace_retains_checked_call_facts,
        fold_over_a_hidden_record_names_the_failed_fact,
        a_labelled_resource_fact_is_refused_by_name,
    ],
    diagnostic_batch_16: [
        memory_history_diagnostic_names_the_store_and_limits_its_claim,
        call_resource_diagnostic_read_shows_state_and_access,
        smart_have_budget_refusal_retains_checked_trace_prefix,
    ],
    diagnostic_batch_17: [
        loop_have_budget_refusal_retains_checked_store_trace,
        ordinary_concise_diagnostics_bound_late_requirement_context,
        ordinary_legacy_diagnostics_bound_late_context_but_traces_remain_full,
    ],
    diagnostic_batch_18: [
        failed_invariant_closure_trace_keeps_its_branch_guard,
        native_view_solve_distinguishes_a_rejected_kernel_query,
    ],
    diagnostic_batch_19: [
        pending_call_obligations_use_shared_goal_printer_and_state_legend,
        function_pointer_load_trace_shows_produced_value_and_read_state,
        call_resource_diagnostic_distinguishes_exact_pointer_arguments_and_states,
        failed_final_known_preserves_its_checked_trace_context,
    ],
    diagnostic_batch_20: [
        known_have_trace_retains_its_written_source_occurrence,
        a_trace_marks_searched_steps_and_their_chosen_arguments,
        rejected_historical_fact_retains_store_prefix,
        failed_selected_close_reports_the_wide_read_goal,
    ],
    diagnostic_batch_21: [
        rejected_wide_historical_fact_retains_store_prefix,
        have_failure_trace_retains_checked_call_prefix,
        budget_stopped_close_retains_its_checked_loop_prefix,
    ],
    diagnostic_batch_22: [
        callback_refinement_hint_with_produced_resource_is_a_checked_proof,
        failed_branch_interface_retains_its_arm_and_written_requirement,
        a_uint32_equality_above_int32_max_prints_in_its_own_type,
    ],
    diagnostic_batch_23: [
        struct_pointer_pointer_ranges_print_pointer_units,
        failed_invariant_after_branch_join_reports_the_join,
        failed_postcondition_after_branch_join_keeps_the_join_trace,
    ],
    diagnostic_batch_24: [
        child_argument_goal_reports_scalar_indices,
        a_failing_tactic_on_an_opened_claim_reports_its_own_source,
        a_static_struct_field_goal_reads_back_with_a_dot,
    ],
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_24")]
fn a_static_struct_field_goal_reads_back_with_a_dot() {
    // A static's declaration reference names the object, so a refused goal
    // about its field is written `"file.c"::static(0).b`, which lowers back
    // to the same read; `->` would take the object for a pointer.
    let fixture = crate::cli::read_mdtest(
        &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/static_struct_fields_by_declaration_reference.md"),
    )
    .unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let inputs = fixture
        .c_sources
        .iter()
        .map(|(name, body)| (name.as_str(), body.as_str()))
        .collect::<Vec<_>>();
    let written = r#"ensures result == "static_fields.c"::static(0).b;"#;
    assert!(source.contains(written), "{source}");
    let false_claim = source.replace(written, r#"ensures "static_fields.c"::static(0).b == 6;"#);
    let error = verify_c_sources(&false_claim, &inputs).expect_err("the field holds 5");
    let report = error.report();
    assert!(
        report.contains(r#""static_fields.c"::static(0).b == 6"#),
        "{report}"
    );
    assert!(!report.contains("static(0)->b"), "{report}");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn an_open_callback_obligation_through_a_static_object_reads_back() {
    // The field of a file-static object read through its address is written
    // `(&"file.c"::static(0))->field`; without the parentheses, `&` would
    // take the address of the field instead of the pointer stored in it.
    let fixture = crate::cli::read_mdtest(
        &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/const_callback_table_abstract.md"),
    )
    .unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let inputs = fixture
        .c_sources
        .iter()
        .map(|(name, body)| (name.as_str(), body.as_str()))
        .collect::<Vec<_>>();
    let step = "    fold(callbacks_storage(&suite));\n    step();\n";
    assert!(source.contains(step), "{source}");
    let with_entries = |propagate: &str, copy: &str| {
        source.replace(
            step,
            &format!(
                "    fold(callbacks_storage(&suite));\n    step() {{\n        requires Propagate({propagate}) by {{ close(); }}\n        requires Copy({copy}) by {{ close(); }}\n    }}\n"
            ),
        )
    };
    let error = verify_c_sources(&with_entries("&propagate", "&copy"), &inputs)
        .expect_err("the function addresses are not the stored field values");
    let field = |name: &str| format!("(&\"abstract_table.c\"::static(0))->{name}");
    let open = format!(
        "it leaves open `Propagate({})`, `Copy({})`",
        field("propagate"),
        field("copy")
    );
    assert!(error.report().contains(&open), "{}", error.report());
    verify_c_sources(&with_entries(&field("propagate"), &field("copy")), &inputs).unwrap_or_else(
        |error| panic!("the listed obligations must read back: {}", error.report()),
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by diagnostic_batch_24")]
fn a_failing_tactic_on_an_opened_claim_reports_its_own_source() {
    // After execution reaches the exit, the first `unfold` of the claim's
    // goal opens the claim's proof, and later tactics run on it. A failure
    // in the second `unfold` names that tactic, not the one that opened it.
    let c = "int f(int p[3]) { return 0; }";
    let source = r#"
        verifying "opened.c";
        predicate sorted(p: int32[], n: int32) {
            sorted_range(p, 0, n)
        }
        predicate sorted_range(p: int32[], lo: int32, hi: int32) {
            forall (i: int32) {
                forall (j: int32) {
                    0 <= i and 0 <= j and lo <= i and i < j and j < hi implies p[i] <= p[j]
                }
            }
        }
        int32 f(int32 p[3]) {
            consumes p[0..3];
            ensures sorted: sorted(p, 1) by {
                step();
                unfold(sorted(p, 1));
                unfold(sorted_range(p, 0, n));
            }
        }
    "#;
    let error =
        verify_c_sources(source, &[("opened.c", c)]).expect_err("`n` is not in scope in the proof");
    assert!(
        error.report().contains("unbound variable `n`"),
        "{}",
        error.report()
    );
    assert_eq!(error.proof_source_site(), Some(("f.sorted", &[2][..])));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn explicit_call_constant_proofs_reject_changed_values() {
    for (name, markdown, before, after) in [
        (
            "call_read_constant_explicit.md",
            include_str!("../../../mdtests/call_read_constant_explicit.md"),
            "*p = 7",
            "*p = 8",
        ),
        (
            "call_byte_constant_explicit.md",
            include_str!("../../../mdtests/call_byte_constant_explicit.md"),
            "{3}",
            "{4}",
        ),
    ] {
        let fixture = crate::cli::parse_mdtest(std::path::Path::new(name), markdown).unwrap();
        let changed: Vec<_> = fixture
            .c_sources
            .iter()
            .map(|(name, source)| {
                let changed = source.replace(before, after);
                assert_ne!(&changed, source);
                (name.as_str(), changed)
            })
            .collect();
        let sources: Vec<_> = changed
            .iter()
            .map(|(name, source)| (*name, source.as_str()))
            .collect();
        assert!(
            verify_c_sources(fixture.click_source.as_deref().unwrap(), &sources).is_err(),
            "the explicit proof must not retain the old constant: {name}"
        );
    }
}

/// A store the implicit tail could not keep a cached element across is
/// marked in the trace with the index fact it lacked, the read after it
/// shows where its history stopped, and the refusal names the statement and
/// the fact the store search spelled.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.71s alone; the failing implicit tail's closing search dominates"]
fn trace_marks_a_dropped_cell_and_the_read_history_stop() {
    let source = r#"verifying "f.c";
        int32 read_first(int32 j) {
            requires 1 <= j;
            requires j <= 4;
            ensures result == 7 or result == 1;
        }
    "#;
    // With `j != 1` the store search proves the fact by a strict bound
    // (`a_store_index_bound_and_disequality_keep_a_cached_element.md`); here
    // `j` may be 1, so the search misses it.
    let c = "int32 read_first(int32 j) { int32 a[4]; a[0] = 7; a[j - 1] = 1; int32 r = a[0]; return r; }";
    with_proof_trace("read_first", || {
        let error = verify_c_sources(source, &[("f.c", c)])
            .expect_err("the store search misses `((j - 1) as int32) != 0`");
        assert!(
            error.message().contains(
                "may have overwritten `a`; it is kept if you state `have ((j - 1) as int32) != 0 by { ... };` before "
            ),
            "{}",
            error.message()
        );
        let trace = error
            .trace_context_report()
            .expect("the checked steps are traced");
        let (store, read) = trace
            .split_once("steps through: r = a[0]")
            .unwrap_or_else(|| panic!("the read is traced: {trace}"));
        assert!(
            store.contains("forgets cached `a` beside the store to `a[…]`: the store keeps it only on the stated fact "),
            "{trace}"
        );
        assert!(
            read.contains("read history stopped after crossing 0 recorded transitions (a read follows at most one)"),
            "{trace}"
        );
    });
}
