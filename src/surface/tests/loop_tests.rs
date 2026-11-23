use super::*;

#[cfg(not(feature = "fast-gate"))]
const SCOPED_LOOP_MODEL_CLICK: &str = r#"verifying "program.c";
spec enum Walk { Active, Done }
function pending(w: Walk) -> int32 { match w { Walk::Active => 1, Walk::Done => 0, } }
resource ghost(id: int32) { field model: Walk; }
tactic stop() {
    consumes dirty: ghost(0);
    produces done: ghost(0);
    ensures pending(done.model) == 0;
} by {
    unfold(dirty);
    let done = fold(ghost(0), { model: Walk::Done });
    have pending(done.model) == 0 by {
        rewrite(done.model, Walk::Done); unfold(pending(Walk::Done)); normalize();
    }
}
void walk(int32 n) {
    owns state: ghost(0);
    requires n >= 0;
    requires state.model == Walk::Active;
    ensures n == 0 or pending(state.model) == 0;
} by {
    loop {
        owns state: ghost(0);
        decreases n;
        invariant n >= 0;
        invariant state.model == Walk::Active;
        initialize by solve();
        maintain by {
            let { done: intermediate } = stop({ dirty: state });
            let { done: state } = stop({ dirty: intermediate });
            have n <= 0 or pending(state.model) == 0 by known();
            step();
        }
        otherwise {
            have n <= 0 or pending(state.model) == 0 by known();
        }
    }
    step();
    have n <= 0 or pending(state.model) == 0 by known();
    solve();
}
"#;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: checks the opt-in loop join through the proof driver"]
fn scoped_loop_facts_keep_the_proof_both_exits_established() {
    let c = "void walk(int n) { while (n > 0) { break; } }";
    super::super::proof::test_with_scoped_loop_exit_facts(|| {
        verify_c_sources(SCOPED_LOOP_MODEL_CLICK, &[("program.c", c)]).unwrap();
    });
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: compares the proof diagnostics of both loop join modes"]
fn scoped_loop_facts_hide_an_intermediate_model_on_a_single_exit() {
    let c = "void walk(int n) { while (1) { break; } }";
    let source = SCOPED_LOOP_MODEL_CLICK.replace(
        "    step();\n    have n <= 0 or pending(state.model) == 0 by known();",
        "    step();\n    have pending(state.model) == 1 by solve();",
    );
    let failed = || {
        with_proof_trace("walk", || {
            verify_c_sources(&source, &[("program.c", c)])
                .expect_err("the reachable break has no pending work")
                .trace_context_report()
                .expect("the proof refusal retains an exact premise list")
                .split_once("premises in scope")
                .expect("the failure records the loop's exported premises")
                .1
                .split("checks observed")
                .next()
                .unwrap()
                .to_owned()
        })
    };
    let legacy = failed();
    let scoped = super::super::proof::test_with_scoped_loop_exit_facts(failed);
    assert!(legacy.contains("pending(value "), "{legacy}");
    assert!(!scoped.contains("pending(value "), "{scoped}");
    assert!(scoped.contains("pending(state.model:Walk), 0"), "{scoped}");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: compares short-circuit proofs with and without an otherwise export"]
fn scoped_loop_facts_keep_a_guard_disjunction_only_when_proved() {
    let c = "void walk(int n, int m) { while (n > 0 && m > 0) { n = 0; } }";
    let source = r#"verifying "program.c";
        void walk(int32 n, int32 m) {
            requires n >= 0;
            ensures true;
        } by {
            loop {
                invariant n >= 0;
                decreases n;
                otherwise { have n <= 0 or m <= 0 by known(); }
            }
            have n <= 0 or m <= 0 by known();
        }
    "#;
    let without_export = source.replace("otherwise { have n <= 0 or m <= 0 by known(); }", "");
    super::super::proof::test_with_scoped_loop_exit_facts(|| {
        verify_c_sources(source, &[("program.c", c)]).unwrap();
        let error = verify_c_sources(&without_export, &[("program.c", c)]).unwrap_err();
        assert!(
            error
                .message()
                .contains("unproved part of the goal: n <= 0 or m <= 0"),
            "{}",
            error.message()
        );
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_00")]
fn separately_declared_guarded_invariants_close_at_the_back_edge() {
    // Keep separately declared guarded members in the gate without the
    // arithmetic search of the large counter-loop scaling audit.
    let c_source = "void guarded_bundle(int x, int y) { int i = 1; while (i > 0) { i = 0; } }";
    let click_source = r#"
        verifying "guarded_bundle.c";
        void guarded_bundle(int32 x, int32 y) {
            requires x == 0;
            requires y == 0;
            ensures x == 0 or x == 1;
            ensures y == 0 or y == 1;
        } by {
            step();
            step();
            loop {
                decreases i;
                invariant x == 0 or x == 1;
                invariant y == 0 or y == 1;
                initialize by solve();
                maintain by {
                    step();
                    have x == 0 or x == 1 by { known(); }
                    have y == 0 or y == 1 by { known(); }
                }
            }
            step();
        }
    "#;
    verify_c_sources(click_source, &[("guarded_bundle.c", c_source)])
        .expect("separately declared guarded invariants should close at the back edge");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_00")]
fn loop_metadata_sees_address_escape_after_the_loop() {
    let c_source = r#"void bounded(int32 n) {
        int32 i = 0;
        while (i < n) { i = i + 1; }
        int32* escaped = &i;
    }"#;
    let source = r#"verifying "bounded.c";
    void bounded(int32 n) { requires n >= 0; ensures true; } by {
        step();
        step();
        loop {
            decreases n - i;
            invariant i >= 0;
            initialize by solve();
            maintain by { step(); }
        }
        solve();
    }"#;
    let error = verify_c_sources(source, &[("bounded.c", c_source)])
        .expect_err("a later address escape still invalidates the ranking component");
    assert!(
        error.message().contains("has its address taken"),
        "{}",
        error.message()
    );
}

/// Collects every `loop` clause reachable from a proof script, including the
/// clauses nested inside another loop's own phase proofs.
fn loop_clauses_in(tactics: &[ProofTactic], clauses: &mut Vec<StructuralClause>) {
    for tactic in tactics {
        match tactic {
            ProofTactic::Loop(clause) => {
                clauses.push(clause.clone());
                for phase in [clause.initialize_proof(), clause.preserve_proof()] {
                    if let Some(nested) = phase.and_then(SourceProof::tactics) {
                        loop_clauses_in(nested, clauses);
                    }
                }
            }
            ProofTactic::Both(both) => {
                loop_clauses_in(&both.left_tactics, clauses);
                loop_clauses_in(&both.right_tactics, clauses);
            }
            ProofTactic::Open(open) => loop_clauses_in(&open.tactics, clauses),
            ProofTactic::If(proof_if) => {
                loop_clauses_in(&proof_if.then_tactics, clauses);
                loop_clauses_in(&proof_if.else_tactics, clauses);
            }
            ProofTactic::Branch(branch) => {
                loop_clauses_in(&branch.then_tactics, clauses);
                loop_clauses_in(&branch.else_tactics, clauses);
            }
            _ => {}
        }
    }
}

/// A loop's retained phase proofs are certificates: expanding a loop fixture
/// must leave `initialize` and `maintain` bodies that contain no smart tactic,
/// so nothing in them is a leaf `ProofCertificate` refuses. In particular the
/// automatic preservation planner's own closer is expanded before the phase is
/// retained; a trailing `solve()` would be rejected here exactly as
/// `ProofCertificate::from_proof_tactics` rejects it.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 7s in the parallel gate"]
fn expanded_loop_phase_proofs_are_certificates() {
    for (filename, function) in [
        // Automatically planned initialization and preservation.
        ("count_to_n_loop_invariant", "count_to_n_loop_invariant"),
        // A ranked loop whose explicit `maintain by` ends at the back edge.
        ("c_decreases_count_up", "count_to_n"),
        // A `maintain by` that proves a member in a `have` first.
        ("loop_invariant_body", "count"),
        // Guarded entry judgments survive more than two declarations.
        ("loop_three_invariant_initialization", "probe_fill"),
        // Different source clauses can share one semantic fact at exit.
        ("loop_semantically_duplicate_invariants", "probe_fill"),
        // Readability certificates name a pointer field through void*.
        ("fork_join_worker_direct_contract", "fill_range"),
    ] {
        assert_loop_phase_expansion_replays(filename, function);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: verifies and replays two complete loop fixtures"]
fn numeric_descent_exit_expansion_replays() {
    for fixture in [
        "loop_numeric_descent_on_exit",
        "loop_numeric_descent_on_generated_exit",
    ] {
        assert_loop_phase_expansion_replays(fixture, "fill");
    }
}

fn assert_loop_phase_expansion_replays(filename: &str, function: &str) {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests")
        .join(format!("{filename}.md"));
    let source = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let click = fixture.click_source.as_deref().unwrap();
    let verified =
        verify_c_sources(click, &sources).unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
    let expanded = expand_checked_grouped_claim(click, &verified, function)
        .unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
    assert!(
        !expanded.contains("close_invariants"),
        "{filename}: {expanded}"
    );
    let parsed = crate::surface::verification::parse_click_file_with_c_sources(&expanded, &sources)
        .unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
    let block = parsed
        .function_blocks()
        .iter()
        .find(|block| block.signature().name() == function)
        .unwrap_or_else(|| panic!("{filename}: expansion lost `{function}`"));
    let mut clauses = block.structural_clauses().to_vec();
    if let Some(tactics) = block.grouped_proof().and_then(SourceProof::tactics) {
        loop_clauses_in(tactics, &mut clauses);
    }
    assert!(!clauses.is_empty(), "{filename}: expansion lost its loop");
    for clause in &clauses {
        for (phase, proof) in [
            ("initialize", clause.initialize_proof()),
            ("maintain", clause.preserve_proof()),
        ] {
            let proof = proof.unwrap_or_else(|| panic!("{filename}: `{phase}` was not expanded"));
            let tactics = proof.tactics().unwrap_or_else(|| {
                panic!("{filename}: `{phase}` stayed a smart proof: {expanded}")
            });
            ProofCertificate::from_proof_tactics(tactics).unwrap_or_else(|error| {
                panic!("{filename}: `{phase}` is not a certificate: {error:?}\n{expanded}")
            });
        }
    }
    verify_c_sources(&expanded, &sources).unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_00")]
fn nested_conjunction_extraction_precedes_explicit_arithmetic_steps() {
    let (click, sources) = loop_fixture("arithmetic_conjunction_extraction");
    let sources = borrowed_sources(&sources);
    let expanded = expand_function_proof_source(&click, &sources, "drain")
        .expect("nested conjunction evidence should expand");
    assert!(expanded.contains("have n >= 0 by"), "{expanded}");
    // The extracted conjunct is the initialization's own fact; the
    // decrease and the exit equality are explicit arithmetic steps.
    assert!(expanded.contains("apply(click::integer::"), "{expanded}");
    assert!(!expanded.contains("normalize()"), "{expanded}");
    let (result, planning) = crate::surface::proof::count_planning_statement_transitions(|| {
        verify_c_sources(&expanded, &sources)
    });
    result.expect("expanded extraction and certificate should recheck");
    assert_eq!(planning, 0, "cold certificate recheck must not plan");

    let tampered_sibling = expanded.replacen(
        "n >= 0 and (n <= 2147483647 and n == n)",
        "n != 0 and (n <= 2147483647 and n == n)",
        1,
    );
    verify_c_sources(&tampered_sibling, &sources)
        .expect_err("a tampered sibling of the extracted conjunction must fail");
}

/// Reads one mdtest fixture's Click source and its C sources.
fn loop_fixture(filename: &str) -> (String, Vec<(String, String)>) {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests")
        .join(format!("{filename}.md"));
    let source = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
    (
        fixture.click_source.clone().unwrap(),
        fixture.c_sources.clone(),
    )
}

fn borrowed_sources(sources: &[(String, String)]) -> Vec<(&str, &str)> {
    sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect()
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn natural_goto_exits_retain_checked_paths_and_expand() {
    for (filename, function) in [
        ("natural_goto_exit_label", "count_down"),
        ("natural_goto_multiple_exit_labels", "count_down_or_stop"),
        ("natural_goto_forward_exit_state", "count_down"),
        (
            "natural_goto_forward_exit_differing_states",
            "count_down_or_stop",
        ),
        (
            "natural_goto_forward_exit_multiple_edges_state",
            "count_down_or_stop",
        ),
    ] {
        let (click, sources) = loop_fixture(filename);
        let sources = borrowed_sources(&sources);
        with_proof_trace(function, || {
            verify_c_sources(&click, &sources).unwrap();
            let trace = accepted_proof_trace(&|_, _| None, &|_, _, _| None, &|_, _, _| false, None)
                .expect("the natural exit must retain an accepted execution path");
            assert!(
                !trace.contains("<no checked simple steps"),
                "{filename}: {trace}"
            );
        });
        let expanded = expand_function_proof_source(&click, &sources, function).unwrap();
        verify_c_sources(&expanded, &sources).unwrap();
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn natural_goto_mixed_return_retains_paths_and_expands() {
    let (click, sources) = loop_fixture("natural_goto_forward_exit_and_return");
    let sources = borrowed_sources(&sources);
    with_proof_trace("count_down_or_stop", || {
        verify_c_sources(&click, &sources).unwrap();
        let trace = accepted_proof_trace(&|_, _| None, &|_, _, _| None, &|_, _, _| false, None)
            .expect("both exits must retain accepted execution paths");
        assert!(!trace.contains("<no checked simple steps"), "{trace}");
    });
    for click in [
        click.clone(),
        click.replace("result == 0 or result == 7", "result == 7 or result == 0"),
    ] {
        let expanded = expand_function_proof_source(&click, &sources, "count_down_or_stop")
            .expect("both checked loop exits must expand");
        assert!(!expanded.contains("if result =="), "{expanded}");
        let (result, planning) =
            crate::surface::proof::count_planning_statement_transitions(|| {
                verify_c_sources(&expanded, &sources)
            });
        result.unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
        assert_eq!(
            planning, 0,
            "expanded proof must cold recheck without planning"
        );
        let forged = expanded.replacen("result == 7", "result == 8", 1);
        verify_c_sources(&forged, &sources)
            .expect_err("a false return contract must remain rejected");
    }
}

/// The lexicographic pivot is an arm choice, not a kernel search. Only the
/// second component decreases on the `j > 0` path and only the first on the
/// other, so the expansion proves the descent member in a `have` at the back
/// edge, proving the arm that holds and closing the disjunction by
/// `known()`, and reverifies through the ordinary entry point.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_00")]
fn lexicographic_ranking_bundle_prints_its_pivot_arm() {
    let (click, sources) = loop_fixture("c_decreases_lexicographic_loop");
    let sources = borrowed_sources(&sources);
    let expanded = expand_function_proof_source(&click, &sources, "phase_count")
        .unwrap_or_else(|error| panic!("lexicographic expansion failed: {}", error.message()));
    assert!(
        !expanded.contains("close_invariants"),
        "the back edge closes as a function's exit does, from `have`s: {expanded}"
    );
    assert!(
        expanded.contains("known();"),
        "each pivot is proved in a `have` and closed by `known`: {expanded}"
    );
    verify_c_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!(
            "the expanded lexicographic proof must reverify: {}\n{expanded}",
            error.message()
        )
    });
}

/// The back edge closes the ranking members the loop's `decreases` clause
/// adds to the bundle, and the smart success expands into the explicit
/// operations that produced it: a `have` per bundle member and one checked
/// ordinary proof per arithmetic member. The printed source
/// must reverify through the ordinary entry point without replanning.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: Integer ranking expansion exceeds 0.5s in the parallel gate"]
fn smart_ranking_closure_expands_to_explicit_bundle_members() {
    let (click, sources) = loop_fixture("c_decreases_count_up");
    let sources = borrowed_sources(&sources);
    let expanded = expand_function_proof_source(&click, &sources, "count_to_n")
        .unwrap_or_else(|error| panic!("count-up expansion failed: {}", error.message()));
    let closer = expanded
        .find("maintain by {")
        .expect("the expansion spells the preservation proof");
    let closer = &expanded[closer..];
    assert!(
        !closer.contains("close_invariants") && !closer.contains("solve();"),
        "the expanded closer must contain no smart leaf: {expanded}"
    );
    assert!(
        closer.contains("have i >= 0 implies i <= n by {"),
        "the expanded closer must prove each bundle member in a `have`: {expanded}"
    );
    let (result, planning) = crate::surface::proof::count_planning_statement_transitions(|| {
        verify_c_sources(&expanded, &sources)
    });
    result.unwrap_or_else(|error| {
        panic!(
            "the expanded count-up proof must reverify: {}\n{expanded}",
            error.message()
        )
    });
    assert_eq!(planning, 0, "explicit certificates must not replan");
}

/// The generated Integer ranking keeps the increment's range proof and
/// operation identity, including when its goal is anchored at loop entry.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: Integer ranking expansion exceeds 0.5s in the parallel gate"]
fn unsigned_integer_ranking_expands_without_search() {
    let (click, sources) = loop_fixture("back_edge_closes_an_unsigned_bound_from_the_guard");
    let sources = borrowed_sources(&sources);
    let expanded = expand_function_proof_source(&click, &sources, "count").unwrap();
    assert!(!expanded.contains("solve("), "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
}

/// A stored byte counter also needs its narrowing's range; the generated
/// proof spells the promoted operation, `(x as int32)`, at iteration entry.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: Integer ranking expansion exceeds 0.5s in the parallel gate"]
fn promoted_integer_ranking_expands_without_search() {
    let (click, sources) = loop_fixture("a_uint8_loop_counter_ranks_as_a_promoted_int32");
    let sources = borrowed_sources(&sources);
    let expanded = expand_function_proof_source(&click, &sources, "clear").unwrap();
    assert!(expanded.contains("(x as int32)"), "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
}

/// A tuple measure's decrease member is a disjunction over pivots, so the
/// smart closer's expansion prints the arm it chose, and that arm is checked
/// like any other: replacing it with the other arm is rejected.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_00")]
fn smart_ranking_closure_expands_its_pivot_arm() {
    let (click, sources) = loop_fixture("c_decreases_nested_loop");
    let sources = borrowed_sources(&sources);
    // The fixture's `maintain` scripts end at the back edge, where the
    // implicit closer, the smart ranking closure, closes each member.
    let expanded = expand_function_proof_source(&click, &sources, "nested_count")
        .unwrap_or_else(|error| panic!("nested-loop expansion failed: {}", error.message()));
    assert!(
        expanded.contains("known();"),
        "the chosen pivot arm must be printed: {expanded}"
    );
    verify_c_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!(
            "the expanded nested-loop proof must reverify: {}\n{expanded}",
            error.message()
        )
    });
}

/// The back edge closes each member with `solve()`, which reads the
/// facts in scope. The nested fixture's outer measure needs `j <= m` at the
/// back edge; dropping the outer `invariant j <= m` leaves that fact in scope
/// from the inner loop's exit, so the ranking member still closes.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_01")]
fn smart_ranking_closure_reads_an_inequality_in_scope() {
    let (click, sources) = loop_fixture("c_decreases_nested_loop");
    let sources = borrowed_sources(&sources);
    verify_c_sources(&click, &sources).expect("the fixture verifies as written");
    let weakened = click.replacen(
        "        invariant j <= m;\n        initialize",
        "        initialize",
        1,
    );
    assert_ne!(weakened, click, "the outer invariant was not removed");
    verify_c_sources(&weakened, &sources).unwrap_or_else(|error| {
        panic!(
            "the inner loop's exit fact closes the ranking member: {}",
            error.message()
        )
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_01")]
fn migrated_negative_loop_fixtures_reach_the_decrease_check() {
    for filename in [
        "c_decreases_rejects_bad_loop_path",
        "c_decreases_rejects_non_decreasing_lexicographic_loop",
        "nested_loop_measure_rejected",
        "c_decreases_rejects_negative_ranking_component",
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(format!("{filename}.md"));
        let source = std::fs::read_to_string(&path).unwrap();
        let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let error = verify_c_sources(fixture.click_source.as_deref().unwrap(), &sources)
            .expect_err("invalid ranking must reject");
        assert!(
            error.message().contains("at the back edge"),
            "{filename}: {}",
            error.message()
        );
        assert!(
            error.message().len() <= 64 * 1024,
            "diagnostic exceeded report cap"
        );
        assert!(!error.message().contains("SymbolicMemory {"));
        assert!(!error.message().contains("ExecutionState {"));
        if error.message().contains("goal:") {
            assert!(error.message().contains("recent premises"));
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn remaining_loop_migration_fixtures_expand_and_recheck() {
    for (filename, function) in [
        ("loop_old_count_invariant", "loop_old_count_invariant"),
        (
            "loop_stdlib_permutation_invariant",
            "loop_stdlib_permutation_invariant",
        ),
        ("loop_preserve_branch", "loop_preserve_branch"),
        ("c_decreases_loop", "drain"),
        ("c_decreases_lexicographic_loop", "phase_count"),
        ("c_decreases_nested_loop", "nested_count"),
        ("fill_tail_keeps_first", "fill_tail_keeps_first"),
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(format!("{filename}.md"));
        let source = std::fs::read_to_string(&path).unwrap();
        let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let click = fixture.click_source.as_deref().unwrap();
        let verified_for_expansion = verify_c_sources(click, &sources)
            .unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
        let expanded = expand_checked_grouped_claim(click, &verified_for_expansion, function)
            .unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
        assert!(!expanded.contains("close_invariants"), "{filename}");
        verify_c_sources(&expanded, &sources)
            .unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_01")]
fn loop_preservation_have_resolves_entry_label_and_expands() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/loop_entry_program_point.md");
    let source = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let click = fixture.click_source.unwrap();
    let verified_for_expansion =
        verify_c_sources(&click, &sources).unwrap_or_else(|e| panic!("{}", e.message()));
    let expanded = expand_checked_grouped_claim(&click, &verified_for_expansion, "drain_to_zero")
        .unwrap_or_else(|e| panic!("{}", e.message()));
    assert!(expanded.contains("loop drain {"), "{expanded}");
    verify_c_sources(&expanded, &sources).unwrap_or_else(|e| panic!("{}", e.message()));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn pointer_loop_increment_emits_checked_equality_proof() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/c_pointer_local_loop_invariant.md");
    let source = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let click = fixture.click_source.unwrap();
    let verified_for_expansion =
        verify_c_sources(&click, &sources).unwrap_or_else(|e| panic!("{}", e.message()));
    let expanded = expand_checked_grouped_claim(&click, &verified_for_expansion, "last_element")
        .unwrap_or_else(|e| panic!("{}", e.message()));
    verify_c_sources(&expanded, &sources).unwrap_or_else(|e| panic!("{}", e.message()));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_01")]
fn grouped_arithmetic_using_expands_to_checked_certificate() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/c_grouped_contract_arithmetic_closer.md");
    let source = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let click = fixture.click_source.unwrap();
    let verified = verify_c_sources(&click, &sources).unwrap();
    let expanded = expand_checked_grouped_claim(&click, &verified, "bump").unwrap();
    assert!(!expanded.contains("solve() using"), "{expanded}");
    let (result, planning) = crate::surface::proof::count_planning_statement_transitions(|| {
        verify_c_sources(&expanded, &sources)
    });
    result.unwrap();
    assert_eq!(planning, 0, "explicit certificate recheck must not plan");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_02")]
fn symbolic_alignment_expands_to_ordinary_proof_and_rechecks_without_planning() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/aligned_symbolic_displacement.md");
    let source = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let click = fixture.click_source.unwrap().replace(
        "    ensures result == 1;\n}",
        "    ensures result == 1;\n} by {\n    step_until(function.exit);\n    have aligned(p + i, 8) by { solve(); }\n    solve();\n}",
    );
    assert!(click.contains("have aligned(p + i, 8)"));
    let verified_for_expansion = verify_c_sources(&click, &sources).unwrap();
    let expanded =
        expand_checked_grouped_claim(&click, &verified_for_expansion, "element_is_aligned")
            .unwrap();
    let (result, planning) = crate::surface::proof::count_planning_statement_transitions(|| {
        verify_c_sources(&expanded, &sources)
    });
    result.unwrap();
    assert_eq!(planning, 0, "ordinary arithmetic recheck must not plan");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2s in the parallel gate"]
fn completed_recursive_loop_bodies_skip_legacy_preplanning_and_recheck() {
    for (filename, function) in [
        ("c_decreases_recursive_in_loop.md", "recursive_loop"),
        (
            "c_decreases_resource_recursive_in_loop.md",
            "zero_walk_loop",
        ),
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(filename);
        let source = std::fs::read_to_string(&path).unwrap();
        let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let explicit = fixture.click_source.unwrap();
        let verified_for_expansion = verify_c_sources(&explicit, &sources)
            .unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
        let expanded = expand_checked_grouped_claim(&explicit, &verified_for_expansion, function)
            .unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
        assert!(!expanded.contains("close_invariants"));
        verify_c_sources(&expanded, &sources)
            .unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_02")]
fn explicit_straight_line_swap_preserves_an_entry_bound() {
    for index in ["0", "j"] {
        let c = format!(
            "int32 swap(int32 p[3], int32 j) {{ int32 tmp; tmp = p[{index}]; p[{index}] = p[{index} + 1]; p[{index} + 1] = tmp; return 0; }}"
        );
        let click = r#"
            import click::separation;
            verifying "swap.c";
            int32 swap(int32 p[3], int32 j) {
                requires j == 0;
                requires p[0] <= p[2];
                requires p[1] <= p[2];
                consumes p[0..3];
                ensures p[0] <= p[2];
            } by {
                step(); step(); step();
                have p[$index] == old(p[$index + 1]) by { normalize(); }
                mark first_written;
                step();
                have to_integer($index) != to_integer($index + 1) by {
                    normalize() using { j == 0; };
                }
                apply(separation::separate_elements(p, $index, $index + 1));
                have separate(statement(3).footprint, memory(p[$index])) by {
                    normalize() using { separate(memory(p[$index]), memory(p[$index + 1])); };
                }
                have p[$index] == at(first_written, p[$index]) by {
                    preserve(memory(p[$index]), statement(3));
                }
                have p[$index] == old(p[$index + 1]) by {
                    rewrite(p[$index], at(first_written, p[$index]));
                    known();
                }
                have p[0] == old(p[1]) by {
                    normalize() using { p[$index] == old(p[$index + 1]); j == 0; };
                }
                have p[2] == old(p[2]) by { normalize(); }
                have p[0] <= p[2] by {
                    rewrite(p[0], old(p[1]));
                    rewrite(p[2], old(p[2]));
                    known();
                }
                step(); solve();
            }
        "#
        .replace("$index", index);
        let sources = [("swap.c", c.as_str())];
        let verified = verify_c_sources(&click, &sources)
            .unwrap_or_else(|e| panic!("index {index}: {}", e.message()));
        let expanded = expand_checked_grouped_claim(&click, &verified, "swap")
            .unwrap_or_else(|e| panic!("index {index}: {}", e.message()));
        assert!(
            !expanded.contains("transport("),
            "index {index}: {expanded}"
        );
        without_implicit_solve_for_claim("swap.contract", || {
            verify_c_sources(&expanded, &sources).map_err(|error| error.report())
        })
        .unwrap_or_else(|e| panic!("index {index}: {e}"));
    }
}

/// A reduction of the second sorting loop, not a replacement for its original C.
/// Existing simple steps suffice when entry index and cell facts are explicit.
fn explicit_swap_loop_fixture(include_entry_bounds: bool) -> (&'static str, String) {
    let c = "int32 swap(int32 p[3]) { int32 j; int32 tmp; j = 0; while (j < 1) { if (p[j + 1] < p[j]) { tmp = p[j]; p[j] = p[j + 1]; p[j + 1] = tmp; } j = j + 1; } return 0; }";
    let entry_bounds = r#"
        have to_integer(j) != 2 by { normalize() using { j == 0; }; }
        have to_integer(j + 1) == 1 by {
            rewrite(j, 0);
            normalize();
        }
        have to_integer(j + 1) != 2 by { rewrite(to_integer(j + 1), 1); normalize(); }
        have to_integer(j + 1) != 0 by { rewrite(to_integer(j + 1), 1); normalize(); }
        apply(click::separation::separate_elements(p, j, 2));
        apply(click::separation::separate_elements(p, j + 1, 2));
        apply(click::separation::separate_elements(p, j + 1, 0));
        have separate(statement(3).statement(0).statement(1).footprint, memory(p[2])) by {
            normalize() using { separate(memory(p[j]), memory(p[2])); };
        }
        have at(statement(3).statement(0).statement(1).exit, p[2]) == at(statement(3).statement(0).statement(1).entry, p[2]) by {
            preserve(memory(p[2]), statement(3).statement(0).statement(1));
        }
        have separate(statement(3).statement(0).statement(2).footprint, memory(p[2])) by {
            normalize() using { separate(memory(p[j + 1]), memory(p[2])); };
        }
        have p[2] == at(statement(3).statement(0).statement(1).exit, p[2]) by {
            preserve(memory(p[2]), statement(3).statement(0).statement(2));
        }
        have p[2] == at(before_swap, p[2]) by {
            rewrite(p[2], at(statement(3).statement(0).statement(1).exit, p[2]));
            known();
        }
        have separate(statement(3).statement(0).statement(2).footprint, memory(p[0])) by {
            normalize() using { separate(memory(p[j + 1]), memory(p[0])); };
        }
        have p[0] == at(statement(3).statement(0).statement(1).exit, p[0]) by {
            preserve(memory(p[0]), statement(3).statement(0).statement(2));
        }
        have at(statement(3).statement(0).statement(1).exit, p[0]) == at(before_swap, p[1]) by {
            normalize() using { at(before_swap, j) == 0; };
        }
        have p[0] == at(before_swap, p[1]) by {
            rewrite(p[0], at(statement(3).statement(0).statement(1).exit, p[0]));
            known();
        }
        have p[1] == at(before_swap, p[0]) by {
            normalize() using { at(before_swap, j) == 0; };
        }
        have p[0] <= p[2] by {
            rewrite(p[0], at(before_swap, p[1]));
            rewrite(p[2], at(before_swap, p[2]));
            known();
        }
        have p[1] <= p[2] by {
            rewrite(p[1], at(before_swap, p[0]));
            rewrite(p[2], at(before_swap, p[2]));
            known();
        }
    "#;
    let entry_bounds = if include_entry_bounds {
        entry_bounds
    } else {
        ""
    };
    let click = format!(
        r#"verifying "swap.c";
        int32 swap(int32 p[3]) {{
            requires p[0] <= p[2]; requires p[1] <= p[2];
            consumes p[0..3]; ensures result == 0;
        }} by {{
            step(); step(); step();
            loop {{
                decreases 1 - j;
                invariant j >= 0 and j <= 1;
                invariant p[0] <= p[2];
                invariant p[1] <= p[2];
                initialize by solve();
                maintain by {{
                    have j == 0 by {{
                        solve() using {{ j < 1; j >= 0; }}
                    }}
                    mark before_swap;
                    if p[j + 1] < p[j] {{
                        step(); step(); step(); step();
                        {entry_bounds}
                        step();
                    }} else {{
                        step(); step(); step();
                    }}
                }}
            }}
            step(); solve();
        }}
    "#
    );
    (c, click)
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2s in the parallel gate"]
fn explicit_swap_loop_preserves_both_entry_bounds_and_expands() {
    let (c, click) = explicit_swap_loop_fixture(true);
    let sources = [("swap.c", c)];
    let verified_for_expansion =
        verify_c_sources(&click, &sources).unwrap_or_else(|e| panic!("{}", e.message()));
    let expanded = expand_checked_grouped_claim(&click, &verified_for_expansion, "swap")
        .unwrap_or_else(|e| panic!("{}", e.message()));
    assert!(!expanded.contains("close_invariants"));
    assert!(!expanded.contains("transport("), "{expanded}");
    without_implicit_solve_for_claim("swap.contract", || {
        verify_c_sources(&expanded, &sources).map_err(|error| error.report())
    })
    .unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn explicit_swap_loop_rejects_missing_entry_bounds() {
    let (c, missing_entry_bounds) = explicit_swap_loop_fixture(false);
    let sources = [("swap.c", c)];
    let error = verify_c_sources(&missing_entry_bounds, &sources).unwrap_err();
    assert!(
        error
            .message()
            .contains("closure body did not prove every invariant obligation")
    );
}

/// Exact observations leave the completed bundle available as a fact. The
/// back edge should retain that direct proof and recheck explicitly.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn observed_member_closure_expands_to_direct_assumptions() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/the_back_edge_closes_a_guarded_member_by_intro.md");
    let source = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let click = fixture.click_source.as_deref().unwrap();
    verify_c_sources(click, &sources).unwrap_or_else(|error| panic!("{}", error.message()));
    let expanded = expand_function_proof_source(click, &sources, "count_run")
        .unwrap_or_else(|error| panic!("{}", error.message()));
    assert!(!expanded.contains("solve();"), "{expanded}");
    assert!(expanded.contains("known();"), "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, &sources))
        .unwrap_or_else(|error| panic!("{}", error.message()));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn explicit_invariant_body_quantified_bubble_census() {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests/bubble_pass3_max_suffix.md");
    let source = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let click = fixture.click_source.as_deref().unwrap();
    verify_c_sources(click, &sources).unwrap();
    let expanded = expand_function_proof_source(click, &sources, "bubble_pass3").unwrap();
    assert!(!expanded.contains("close_invariants"));
    verify_c_sources(&expanded, &sources).unwrap();
}

/// The old/current state body verifies and expands on the ordinary stack.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn explicit_invariant_body_copy3_checks_and_expands() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests/copy3_array_demo.md");
    let source = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let click = fixture.click_source.as_deref().unwrap();
    verify_c_sources(click, &sources).unwrap();
    let expanded = expand_function_proof_source(click, &sources, "copy3").unwrap();
    assert!(!expanded.contains("close_invariants"));
    verify_c_sources(&expanded, &sources).unwrap_or_else(|error| panic!("{}", error.message()));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_02")]
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
                loop count {
                    decreases 3 - i;
                    invariant i >= 0;
                    invariant i <= 3;
                    initialize by solve();
                    maintain by {
                        step();
                    }
                }
                have at(count.entry, i) == 0 by solve();
                have at(count.exit, i) == 3 by solve();
                step();
                solve();
            }
        "#;

    let verified = verify_c_sources(click_source, &[("count_to_three.c", c_source)])
        .expect("frontier-local loop proof should verify from its actual entry frontier");

    assert_eq!(verified.len(), 1);
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_02")]
fn individual_loop_proof_has_no_whole_claim_acceptance_check() {
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
            ensures result == 3 by {
                step();
                step();
                loop count {
                    decreases 3 - i;
                    invariant i >= 0;
                    invariant i <= 3;
                    initialize by solve();
                    maintain by {
                        step();
                    }
                }
                have at(count.entry, i) == 0 by solve();
                have at(count.exit, i) == 3 by solve();
                step();
                solve();
            }
        }
    "#;
    let sources = [("count_to_three.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c_sources(click_source, &sources));
    let verified = verified.expect("the individual loop proof should verify once");
    assert!(events.iter().all(|event| !matches!(
        event,
        crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
            if matches!(
                name.as_str(),
                "whole-claim certificate construction" | "whole-claim certificate validation"
            )
    )));
    verified[0]
        .expanded_proof_certificate()
        .expect("the compatibility proof should retain expansion evidence");

    let rewritten = expand_c_claim_source(
        click_source,
        &sources,
        "count_to_three",
        ContractProofClaim::Ensure(0),
    )
    .expect("the retained individual loop proof should expand");
    verify_c_sources(&rewritten, &sources)
        .expect("the rewritten individual loop proof should verify normally");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_03")]
fn loop_initialization_theorem_search_retains_checked_fixed_state_proof() {
    let c_source = r#"
            int32 initialize_with_theorem(int32 x) {
                while (x < 1) {
                    x = 0;
                }
                return x;
            }
        "#;
    let click_source = r#"
            verifying "initialize_with_theorem.c";

            predicate acceptable(x: int32) {
                x >= 0
            }

            theorem nonnegative_is_acceptable(x: int32) {
                requires x >= 0;
                ensures acceptable(x) by {
                    unfold(acceptable(x));
                    solve();
                }
            }

            int32 initialize_with_theorem(int32 x) diverges {
                requires x >= 0;
                ensures acceptable(result);
            } by {
                loop diverges {
                    invariant acceptable(x);
                    initialize by {
                        apply(nonnegative_is_acceptable(x));
                        solve();
                    }
                    maintain by {
                        step();
                        apply(nonnegative_is_acceptable(x));
                        solve();
                    }
                }
                step();
                unfold(acceptable(x));
                solve();
            }
        "#;

    let verified = verify_c_sources(click_source, &[("initialize_with_theorem.c", c_source)]);
    verified.expect("loop initialization theorem search should verify through Proof");

    let offset = click_source
        .find("apply(nonnegative_is_acceptable(x));")
        .expect("initialization proof should contain its smart theorem application");
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let expanded = expand_c_tactic_source_at(
        click_source,
        &[("initialize_with_theorem.c", c_source)],
        line,
        column,
    )
    .expect("the retained initialization theorem step should expand");
    assert!(
        expanded.contains("apply(nonnegative_is_acceptable(x));"),
        "{expanded}"
    );
    verify_c_sources(&expanded, &[("initialize_with_theorem.c", c_source)])
        .expect("expanded initialization theorem application should independently verify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_03")]
fn loop_initialization_solve_retains_checked_fixed_state_proof() {
    let c_source = r#"
            int32 initialize_by_solve(int32 x) {
                while (x < 1) {
                    x = 0;
                }
                return x;
            }
        "#;
    let click_source = r#"
            verifying "initialize_by_solve.c";

            int32 initialize_by_solve(int32 x) diverges {
                requires x >= 0;
                ensures result >= 0;
            } by {
                loop diverges {
                    invariant x >= 0;
                    initialize by solve();
                    maintain by {
                        step();
                    }
                }
                step();
                solve();
            }
        "#;

    let verified = verify_c_sources(click_source, &[("initialize_by_solve.c", c_source)]);
    verified.expect("loop initialization solve should verify through Proof");

    let offset = click_source
        .find("initialize by solve()")
        .expect("initialization proof should contain its smart solve")
        + "initialize by ".len();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let expanded = expand_c_tactic_source_at(
        click_source,
        &[("initialize_by_solve.c", c_source)],
        line,
        column,
    )
    .expect("the retained initialization closer should expand");
    assert!(!expanded.contains("initialize by solve()"), "{expanded}");
    assert!(expanded.contains("known();"), "{expanded}");
    verify_c_sources(&expanded, &[("initialize_by_solve.c", c_source)])
        .expect("expanded initialization closer should independently verify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_03")]
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

    let error = verify_c_sources(click_source, &[("count_to_three.c", c_source)])
        .expect_err("loop should not seek forward from a non-loop frontier");

    assert!(
        error
            .message()
            .contains("requires the execution frontier to be at a loop"),
        "{}",
        error.message()
    );
    assert!(error.message().contains("region(0)"), "{}", error.message());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_03")]
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

    let error = verify_c_sources(click_source, &[("count_once.c", c_source)])
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_04")]
fn frontier_loop_preservation_reports_a_rest_that_does_not_run() {
    // The script stops one statement short; the rest of the body runs
    // implicitly, except that `1 / (i - 1)` may divide by zero, so the path
    // is reported at the frontier the script reached, with the reason.
    let c_source = r#"
            int32 count_once() {
                int32 i;
                i = 0;
                while (i < 1) {
                    i = i + 1;
                    i = 1 / (i - 1);
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
                    maintain by {
                        step();
                    }
                }
            }
        "#;

    let error = verify_c_sources(click_source, &[("count_once.c", c_source)])
        .expect_err("a rest of the body that does not run is reported");
    let message = error.message();
    assert!(
        message.contains("stopped inside the loop body")
            && message.contains("the frontier is at statement")
            && message.contains("still ahead on this path: the body's end")
            && message.contains("the rest of the body did not run from there"),
        "{message}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_04")]
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
                    decreases 3 - i;
                    invariant i >= 0;
                    invariant i <= 3;
                    initialize by solve();
                    maintain by {
                        step();
                        step();
                    }
                }
                step();
                solve();
            }
        "#;

    verify_c_sources(click_source, &[("count_to_three.c", c_source)])
        .expect("frontier-local loop should bind a C `for` lowered to a kernel loop");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_04")]
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
                        decreases 2 - i;
                        invariant i >= 0;
                        invariant i <= 2;
                        initialize by solve();
                        maintain by {
                            step();
                        }
                    }
                    step();
                    solve();
                } else {
                    step();
                    step();
                    step();
                    solve();
                }
            }
        "#;

    verify_c_sources(click_source, &[("branch_count.c", c_source)])
        .expect("frontier-local loop should use the branch's actual execution context");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_04")]
fn frontier_loop_binding_replaces_scope_without_merging_declarations() {
    let parsed = parse(
        r#"
        verifying "count.c";
        int32 count(int32 i) { ensures result >= 0; } by {
            loop {
                invariant i >= bound;
                invariant i >= bound;
                initialize by solve();
                maintain by solve();
            }
        }
    "#,
    )
    .unwrap();
    let function = &parsed.function_blocks()[0];
    let ProofTactic::Loop(template) = &function.grouped_proof().unwrap().tactics().unwrap()[0]
    else {
        panic!("expected the loop template");
    };
    let value = |n| ContractExpression::ProgramExpression(ProgramExpression::Value(int32(n)));
    let outer = template.with_scope(BTreeMap::from([("bound".to_string(), value(0))]));
    let inner = template.with_scope(BTreeMap::from([("bound".to_string(), value(1))]));
    let initial = function
        .with_bound_frontier_loop_clauses(&[outer.bound_to_loop(0), outer.bound_to_loop(1)]);
    let rebound = initial.with_frontier_loop_clause(&inner, 1);
    let repeated = rebound.with_bound_frontier_loop_clauses(&[inner.bound_to_loop(1)]);
    assert_eq!(initial.structural_clauses().len(), 2);
    assert_eq!(rebound.structural_clauses(), repeated.structural_clauses());
    assert_eq!(repeated.structural_clauses().len(), 2);
    assert_eq!(
        repeated.structural_clauses().to_vec()[0],
        outer.bound_to_loop(0)
    );
    assert_eq!(
        repeated.structural_clauses().to_vec()[1],
        inner.bound_to_loop(1)
    );
    assert_eq!(repeated.structural_clauses().to_vec()[1].items().len(), 2);
    assert_eq!(
        initial.structural_clauses().to_vec()[1],
        outer.bound_to_loop(1)
    );
    assert_ne!(
        initial.structural_clauses().to_vec()[1]
            .resolved()
            .unwrap()
            .items(),
        repeated.structural_clauses().to_vec()[1]
            .resolved()
            .unwrap()
            .items()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
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
                    decreases 2 - i;
                    invariant i >= 0;
                    invariant i <= 2;
                    initialize by solve();
                    maintain by {
                        step();
                        loop {
                            decreases 2 - j;
                            invariant j >= 0;
                            invariant j <= 2;
                            initialize by solve();
                            maintain by {
                                step();
                            }
                        }
                        step();
                    }
                }
                step();
                solve();
            }
        "#;

    let sources = [("nested_count.c", c_source)];
    let verified = verify_c_sources(click_source, &sources)
        .expect("nested loop proofs should be scoped to their respective frontiers");
    let expanded = expand_checked_grouped_claim(click_source, &verified, "nested_count")
        .expect("nested loop proofs should expand");
    verify_c_sources(&expanded, &sources).expect("expanded nested loops should verify");
    let repeated = expand_function_proof_source(&expanded, &sources, "nested_count")
        .expect("expanded nested loops should remain expandable");
    assert_eq!(repeated, expanded);
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_05")]
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
                consumes p[0..n];
                ensures result == n;
            } by {
                step();
                step();
                loop {
                    decreases n - i;
                    invariant i >= 0 and i <= n;
                    initialize by solve();
                    maintain by {
                        step();
                        step();
                    }
                }
                step();
                solve();
            }
        "#;
    let preserve_step = click_source
        .find("maintain by {")
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

    let expanded = expand_c_tactic_source_at(click_source, &[("fill_n.c", c_source)], line, column)
        .expect("the preservation store should expand");

    let indent = &click_source[preserve_step + 1 - column..preserve_step];
    let expected = format!(
        "{}step() by {{\n{indent}    known();\n{indent}}}{}",
        &click_source[..preserve_step],
        &click_source[preserve_step + "step();".len()..],
    );
    assert_eq!(expanded, expected);
    verify_c_sources(&expanded, &[("fill_n.c", c_source)])
        .expect("the expanded store should use the invariant at the current frontier");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_05")]
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
                    initialize by solve();
                    maintain by {
                        have 0 <= to_integer(n - 1) by {
                            solve() using { n > 0; }
                        }
                        step();
                    }
                }
                step();
                solve();
            }
        "#;

    let (session, _) = ProgramVerificationSession::new(click_source, &[("drain.c", c_source)])
        .expect("frontier-local loop should retain structural termination checking");
    assert!(session.function_termination_is_verified("drain"));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_05")]
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
                    decreases n - i;
                    invariant i >= 0;
                    invariant i <= n;
                }
                step();
                solve();
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
        expand_c_tactic_source_at(click_source, &[("count_to_n.c", c_source)], line, column)
            .expect("the loop keyword should expand all omitted phase automation");

    assert!(expanded.contains("initialize by {"), "{expanded}");
    assert!(expanded.contains("maintain by {"), "{expanded}");
    verify_c_sources(&expanded, &[("count_to_n.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "the expanded frontier-local loop should freshly check: {}\n{expanded}",
            error.message()
        )
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_05")]
fn loop_exit_solve_expands_invariant_conjuncts_explicitly() {
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
                ensures result == n and result >= 0;
            } by {
                step();
                step();
                loop {
                    decreases n - i;
                    invariant i >= 0 and i <= n;
                }
                step();
                solve();
            }
        "#;
    let solve_offset = click_source
        .rfind("solve();")
        .expect("proof should contain its final solve");
    let line = click_source[..solve_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = solve_offset
        - click_source[..solve_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c_tactic_source_at(click_source, &[("count_to_n.c", c_source)], line, column)
            .expect("loop-exit solve should expand through explicit invariant conjuncts");

    assert!(
        expanded.contains("have at(loop(0).exit, i) <= at(loop(0).exit, n) by"),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(click::integer::int32_less_equal_and_not_less_than_implies_equal(at(loop(0).exit, i), at(loop(0).exit, n)));"),
        "{expanded}"
    );
    assert!(!expanded.contains("normalize()"), "{expanded}");
    verify_c_sources(&expanded, &[("count_to_n.c", c_source)])
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.report()));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_06")]
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
                    decreases 3 - i;
                    invariant i >= 0;
                    invariant i <= 3;
                }
                step();
                solve();
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

    let expanded = expand_c_tactic_source_at(
        click_source,
        &[("count_to_three.c", c_source)],
        line,
        column,
    )
    .expect("the post-loop step should expand independently");

    verify_c_sources(&expanded, &[("count_to_three.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "post-loop expansion should not leak loop-region tactics: {}\n{expanded}",
            error.message()
        )
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_06")]
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
                    decreases 3 - i;
                    invariant i >= 0;
                    invariant i <= 3;
                    initialize by solve();
                    maintain by {
                        step();
                    }
                }
                step();
                solve();
            }
        "#;
    let initialize_solve = click_source
        .find("initialize by solve()")
        .expect("proof should contain explicit initialization")
        + "initialize by ".len();
    let line = click_source[..initialize_solve]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = initialize_solve
        - click_source[..initialize_solve]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let inventory = c_smart_tactic_source_sites(click_source, &[("count_to_three.c", c_source)])
        .expect("frontier-local nested tactics should be inventoried without verification");
    let matching_inventory = inventory
        .iter()
        .filter(|site| {
            c_tactic_source_position(
                click_source,
                &[("count_to_three.c", c_source)],
                &site.claim_label,
                site.source_index,
            )
            .is_ok_and(|position| position.line == line && position.column == column)
        })
        .collect::<Vec<_>>();
    assert_eq!(matching_inventory.len(), 1, "{inventory:?}");
    assert_eq!(matching_inventory[0].tactic_name, "solve");

    let expanded = expand_c_tactic_source_at(
        click_source,
        &[("count_to_three.c", c_source)],
        line,
        column,
    )
    .expect("explicit initialization tactic should expand at its own source location");

    assert!(!expanded.contains("initialize by solve()"), "{expanded}");
    assert!(expanded.contains("maintain by {"), "{expanded}");
    verify_c_sources(&expanded, &[("count_to_three.c", c_source)])
        .expect("expanded explicit initialization tactic should freshly check");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_06")]
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
                    initialize by solve();
                    maintain by {
                        have 0 <= to_integer(n - 1) by {
                            solve() using { n > 0; }
                        }
                        step();
                    }
                }
                step();
                solve();
            }
        "#;

    let tactics = super::proof::capture_program_tactic_expansion(
        click_source,
        &[("drain.c", c_source)],
        super::expansion::ProofSite::FunctionClaim {
            function_name: "drain".to_string(),
            claim: ContractProofClaim::Grouped,
        },
        1,
        &[],
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_06")]
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
                    decreases 3 - i;
                    invariant i >= 0;
                    invariant i <= 3;
                    initialize by solve();
                    maintain by {
                        step();
                    }
                }
                step();
                solve();
            }
        "#;
    let preserve_step = click_source
        .find("maintain by {")
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

    let expanded = expand_c_tactic_source_at(
        click_source,
        &[("count_to_three.c", c_source)],
        line,
        column,
    )
    .expect("preservation step should expand at its own source location");

    // A bare `step()` is a simple tactic: expanding it leaves the source as
    // written, and the loop's other phases stay untouched.
    assert_eq!(expanded, click_source);
    assert!(expanded.contains("initialize by solve()"), "{expanded}");
    verify_c_sources(&expanded, &[("count_to_three.c", c_source)])
        .expect("expanded preservation step should freshly check");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_07")]
fn explicit_loop_closer_cannot_bypass_proof_owned_bundle_check() {
    let c_source = r#"
            int32 overshoot() {
                int32 i;
                i = 0;
                while (i < 1) {
                    i = i + 2;
                }
                return i;
            }
        "#;
    let click_source = r#"
            verifying "overshoot.c";

            int32 overshoot() {
                ensures result == 2;
            } by {
                step();
                step();
                loop {
                    invariant i >= 0;
                    invariant i <= 1;
                    initialize by solve();
                    maintain by {
                        step();
                    }
                }
                step();
                solve();
            }
        "#;

    let error = verify_c_sources(click_source, &[("overshoot.c", c_source)])
        .expect_err("the explicit closer must not authorize a false invariant bundle");
    assert!(
        error
            .message()
            .contains("closure body did not prove every invariant obligation"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_07")]
fn body_final_branch_preservation_completes_at_typed_back_edge_boundary() {
    // The loop body ends with a C `if` whose arms fall through directly to
    // the back-edge. The preservation frontier owns exactly the body's
    // statement tree, so both arms and their join complete at the typed
    // region boundary; no synthetic statement after the branch exists for a
    // join continuation to rest on. Explicit-branch, automatic-planner, and
    // deliberately broken variants all exercise that boundary.
    let c_source = r#"
            int32 flip_to_n(int32 n) {
                int32 i;
                int32 parity;
                i = 0;
                parity = 0;
                while (i < n) {
                    i = i + 1;
                    if (parity < 1) {
                        parity = 1;
                    } else {
                        parity = 0;
                    }
                }
                return parity;
            }
        "#;
    let template = r#"
            verifying "flip_to_n.c";

            int32 flip_to_n(int32 n) {
                ensures result >= 0;
            } by {
                step();
                step();
                step();
                step();
                loop {
                    decreases n - i;
                    invariant i >= 0;
                    invariant parity >= 0 and parity <= 1;
                    initialize by solve();
                    {preserve}
                }
                step();
                solve();
            }
        "#;
    let explicit = template.replace(
        "{preserve}",
        r#"maintain by {
                        step();
                        branch ensuring { fact parity >= 0 and parity <= 1; } { true => { step(); } false => { step(); } }
                    }"#,
    );
    let sources = [("flip_to_n.c", c_source)];
    verify_c_sources(&explicit, &sources).expect(
        "explicit body-final branch preservation should complete at the typed back-edge boundary",
    );

    // The omitted-phase planner reaches the same boundary and closes the whole
    // back-edge bundle there, including the two members the `decreases` clause
    // adds. Both arms carry the C branch condition as a named premise, so the
    // ranking members are ordinary arithmetic steps over the loop head's
    // own clauses.
    let automatic = template.replace("{preserve}", "");
    verify_c_sources(&automatic, &sources)
        .expect("automatic preservation should plan through the body-final branch to the boundary");

    let broken = template.replace(
        "{preserve}",
        r#"maintain by {
                        step();
                        branch ensuring { fact parity >= 0 and parity <= 1; } { true => { step(); } false => { step(); } }
                    }"#,
    );
    let broken = broken.replace(
        "invariant parity >= 0 and parity <= 1;",
        "invariant parity <= 0;",
    );
    let error = verify_c_sources(&broken, &sources)
        .expect_err("an invariant violated through one body-final arm must fail preservation");
    assert!(
        format!("{error:?}").contains("invariant"),
        "the failure should name the invariant bundle: {error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_07")]
fn frontier_local_loop_exit_bound_weakens_to_a_looser_ensures() {
    // The negated loop guard leaves `i >= 3` at the loop's exit. The checked
    // outcome `solve` must retain a checkable proof of the *looser* bounds
    // `result >= 1` and `result <= 5` (constant-bound weakening, expanded as
    // explicit `arithmetic() using` certificates), not only the exact
    // `result == 3`.
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
                ensures result >= 1;
                ensures result <= 5;
            } by {
                step();
                step();
                loop {
                    decreases 3 - i;
                    invariant i >= 0;
                    invariant i <= 3;
                    initialize by solve();
                    maintain by {
                        step();
                    }
                }
                step();
                solve();
            }
        "#;

    verify_c_sources(click_source, &[("count_to_three.c", c_source)]).expect(
        "the checked outcome solve should weaken the loop-exit bound to the looser ensures",
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_07")]
fn whole_claim_expansion_reconstructs_nested_decided_branch_and_loop_match() {
    let c_source = r#"
        int32 selected_then_loop(int32 x) {
            if (x < 0) {
                x = 1;
            } else {
                x = 2;
            }
            while (x == 1) {
                x = 2;
            }
            return x;
        }
    "#;
    let click_source = r#"
        spec enum Marker { Active, Inactive }
        function marker() -> Marker { Marker::Active }

        verifying "selected_then_loop.c";

        int32 selected_then_loop(int32 x) {
            requires x < 0;
            ensures result >= 1;
        } by {
            have marker() != Marker::Inactive by {
                unfold(marker());
                known();
            }
            match marker() {
                Marker::Active => {
                    branch { true => { step(); } false => { step(); } }
                    loop {
                        decreases 2 - to_integer(x);
                        invariant x >= 1;
                        invariant x <= 2;
                        initialize by solve();
                        maintain by {
                            have marker() != Marker::Inactive by {
                                unfold(marker());
                                known();
                            }
                            match marker() {
                                Marker::Active => {
                                    step();
                                },
                                Marker::Inactive => {
                                    contradiction(marker() == Marker::Inactive);
                                },
                            }
                        }
                    }
                    step();
                    solve();
                },
                Marker::Inactive => {
                    contradiction(marker() == Marker::Inactive);
                },
            }
        }
    "#;
    let sources = [("selected_then_loop.c", c_source)];

    verify_c_sources(click_source, &sources).expect("the reduced source proof should verify");
    let expanded = expand_c_claim_source(
        click_source,
        &sources,
        "selected_then_loop",
        ContractProofClaim::Ensure(0),
    )
    .expect("the reduced whole claim should expand");
    verify_c_sources(&expanded, &sources)
        .expect("the reduced whole-claim expansion should independently verify");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn loop_exit_duplicate_invariants_verify_and_reject_false_claims() {
    let c = r#"int32 count(int32 n) {
        int32 i = 0;
        while (i < n) { i = i + 1; }
        return i;
    }"#;
    let source = r#"
        verifying "count.c";
        int32 count(int32 n) {
            requires 0 <= n and n <= 1000;
            ensures result == n;
        } by {
            step(); step();
            loop {
                decreases n - i;
                invariant 0 <= i and i <= n;
                invariant 0 == 0;
                invariant 1 == 1;
                invariant forall (k: int32) { k == k };
            }
            step(); solve();
        }
    "#;
    for source in [
        source.to_owned(),
        source.replace("invariant 1 == 1;", "invariant 0 == 0;"),
    ] {
        let verified = verify_c_sources(&source, &[("count.c", c)]).unwrap();
        let expanded = expand_checked_grouped_claim(&source, &verified, "count").unwrap();
        verify_c_sources(&expanded, &[("count.c", c)]).unwrap();
        let false_claim = source.replace("ensures result == n;", "ensures result == n + 1;");
        let error = verify_c_sources(&false_claim, &[("count.c", c)]).unwrap_err();
        assert!(
            error.message().contains("unclosed goal"),
            "{}",
            error.message()
        );
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_08")]
fn changed_break_exit_does_not_label_head_invariants_as_exit_facts() {
    let (source, sources) = loop_fixture("loop_body_break_exit_joined_state");
    let sources = borrowed_sources(&sources);
    let source = source.replace(
        "invariant r == 0;",
        r#"invariant r == 0;
        invariant 0 == 0;
        invariant 1 == 1;
        invariant forall (k: int32) { k == k };"#,
    );
    let verified = verify_c_sources(&source, &sources).unwrap();
    let expanded = expand_checked_grouped_claim(&source, &verified, "assign_then_break").unwrap();
    verify_c_sources(&expanded, &sources).unwrap();
    for fact in ["r == 0", "at(loop(0).exit, r) == at(loop(0).exit, 0)"] {
        let false_have = source.replace(
            "    step();\n    solve();",
            &format!("    have {fact} by {{ known(); }}\n    step();\n    solve();"),
        );
        assert_ne!(source, false_have);
        let error = verify_c_sources(&false_have, &sources).unwrap_err();
        assert!(
            error
                .message()
                .contains("`known()` could not close the current goal"),
            "{}",
            error.message()
        );
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_08")]
fn conditional_loop_resources_parse_print_and_resolve_scope() {
    let source = r#"
        verifying "conditional.c";
        int32 conditional(int32 *p, int32 *q, int32 n) {
            ensures result == 0;
        } by {
            loop {
                decreases n;
                if n > bound {
                    owns p[0..1];
                    views q[0..1];
                }
                invariant n >= 0;
            }
        }
    "#;
    let parsed = parse(source).expect("conditional loop resources parse");
    let function = &parsed.function_blocks()[0];
    let tactics = function.grouped_proof().unwrap().tactics().unwrap();
    let ProofTactic::Loop(clause) = &tactics[0] else {
        panic!("loop");
    };
    assert_eq!(clause.resources().len(), 2);
    assert!(
        matches!(&clause.resources()[0], ResourceClause::Conditional { resource, .. } if matches!(resource.as_ref(), ResourceClause::OwnMemory(_)))
    );
    assert!(
        matches!(&clause.resources()[1], ResourceClause::Conditional { resource, .. } if matches!(resource.as_ref(), ResourceClause::ViewMemory(_)))
    );
    let printed = crate::surface::printing::format_partial_tactic_sequence(tactics);
    let reparsed = parse(&format!(r#"verifying "conditional.c";
        int32 conditional(int32 *p, int32 *q, int32 n) {{ ensures result == 0; }} by {{ {printed} }}"#)).unwrap();
    assert_eq!(
        reparsed.function_blocks()[0]
            .grouped_proof()
            .unwrap()
            .tactics()
            .unwrap(),
        tactics
    );
    let scoped = clause.with_scope(BTreeMap::from([(
        "bound".to_string(),
        ContractExpression::ProgramExpression(ProgramExpression::Value(int32(4))),
    )]));
    let resolved = scoped.resolved().unwrap();
    assert_ne!(resolved.resources(), clause.resources());
    let ResourceClause::Conditional { condition, .. } = &resolved.resources()[0] else {
        panic!("conditional");
    };
    assert_eq!(
        crate::surface::printing::source_click_proposition(condition),
        "n > 4"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_08")]
fn conditional_loop_resources_reject_unsupported_binding_and_body_items() {
    for (body, expected) in [
        (
            "owns item: payload(p);",
            "conditional loop resource binders are not supported",
        ),
        (
            "invariant n >= 0;",
            "conditional loop contracts accept `owns` or `views`",
        ),
        ("", "conditional loop contract must contain"),
    ] {
        let source = format!(
            r#"verifying "conditional.c";
            int32 conditional(int32 *p, int32 n) {{ ensures result == 0; }} by {{
                loop {{ if n > 0 {{ {body} }} }}
            }}"#
        );
        let error = parse(&source).expect_err("unsupported conditional declaration");
        assert!(error.message().contains(expected), "{error:?}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 7s in the parallel gate"]
fn loop_return_closers_expand_in_their_preservation_arms() {
    for (fixture, function) in [
        (
            "a_summarized_loop_body_return_is_certified_with_its_value",
            "f",
        ),
        ("loop_return_closes_in_preserve_arm", "f"),
        ("nested_loop_return_survives_outer_backedge", "f"),
        ("natural_goto_forward_exit_and_return", "count_down_or_stop"),
    ] {
        let (click, sources) = loop_fixture(fixture);
        let sources = borrowed_sources(&sources);
        verify_c_sources(&click, &sources).unwrap();
        for site in c_smart_tactic_source_sites(&click, &sources).unwrap() {
            let position =
                c_tactic_source_position(&click, &sources, &site.claim_label, site.source_index)
                    .unwrap();
            let expanded =
                expand_c_tactic_source_at(&click, &sources, position.line, position.column)
                    .unwrap_or_else(|error| {
                        panic!("{fixture} {}: {}", site.source_index, error.message())
                    });
            verify_c_sources(&expanded, &sources).unwrap();
        }
        let expanded = expand_function_proof_source(&click, &sources, function).unwrap();
        assert!(!expanded.contains("if result =="), "{expanded}");
        assert!(
            c_smart_tactic_source_sites(&expanded, &sources)
                .unwrap()
                .is_empty(),
            "{expanded}"
        );
        let (result, planning) =
            crate::surface::proof::count_planning_statement_transitions(|| {
                verify_c_sources(&expanded, &sources)
            });
        result.unwrap();
        assert_eq!(
            planning, 0,
            "{fixture}: expanded proof must cold recheck without planning"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn nested_loop_return_keeps_the_inner_arms_closer() {
    let c = "int32 f(int32 n) { while (1) { while (1) { return 7; } } }";
    let click = r#"
verifying "nested.c";
int32 f(int32 n) {
    requires n == 5;
    ensures result == 7;
} by {
    loop { decreases 1; invariant n == 5;
        maintain by {
            loop { decreases 1; invariant n == 5;
                maintain by { step(); have result == 7 by solve(); solve(); }
            }
        }
    }
}
"#;
    let sources = [("nested.c", c)];
    verify_c_sources(click, &sources).unwrap();
    let false_arm = click.replace("have result == 7", "have result == 8");
    assert!(
        verify_c_sources(&false_arm, &sources)
            .unwrap_err()
            .message()
            .contains("could not establish `result == 8`")
    );
    for site in c_smart_tactic_source_sites(click, &sources).unwrap() {
        let position =
            c_tactic_source_position(click, &sources, &site.claim_label, site.source_index)
                .unwrap();
        let expanded =
            expand_c_tactic_source_at(click, &sources, position.line, position.column).unwrap();
        verify_c_sources(&expanded, &sources).unwrap();
    }
    let expanded = expand_function_proof_source(click, &sources, "f").unwrap();
    assert!(
        c_smart_tactic_source_sites(&expanded, &sources)
            .unwrap()
            .is_empty()
    );
    let (result, planning) = crate::surface::proof::count_planning_statement_transitions(|| {
        verify_c_sources(&expanded, &sources)
    });
    result.unwrap();
    assert_eq!(planning, 0);
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_08")]
fn loop_return_closers_do_not_require_distinct_result_values() {
    let (click, sources) = loop_fixture("loop_return_closes_in_preserve_arm");
    let click = click
        .replace(
            "ensures result == 5 or result == 7;",
            "ensures result == 7;",
        )
        .replace("have result == 5;", "have result == 7;");
    assert!(
        click.contains("have result == 7;"),
        "the fixture states the returned value"
    );
    let sources = sources
        .into_iter()
        .map(|(name, source)| (name, source.replace("return i;", "return 7;")))
        .collect::<Vec<_>>();
    let sources = borrowed_sources(&sources);
    let verified_for_expansion = verify_c_sources(&click, &sources).unwrap();
    let expanded = expand_checked_grouped_claim(&click, &verified_for_expansion, "f").unwrap();
    assert!(!expanded.contains("if result =="), "{expanded}");
    verify_c_sources(&expanded, &sources).unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn loop_return_inside_branch_retains_its_fact_ancestry() {
    let c = "int32 f(int32 n) { if (n > 0) { int32 i = 0; while (i < n) { if (i == 2) return 7; i++; } return i; } else { return 7; } }";
    let click = r#"
verifying "branch.c";
int32 f(int32 n) {
    requires n >= 0;
    ensures result == n or result == 7;
} by {
    branch {
        true => {
            step(); step();
            loop { decreases n-i; invariant i >= 0; invariant i <= n; }
            step(); have result == n by solve(); solve();
        }
        false => { step(); solve(); }
    }
}
"#;
    let sources = [("branch.c", c)];
    let verified_for_expansion = verify_c_sources(click, &sources).unwrap();
    let expanded = expand_checked_grouped_claim(click, &verified_for_expansion, "f").unwrap();
    verify_c_sources(&expanded, &sources).unwrap();
    let false_contract = click.replace("result == n or result == 7", "result == n");
    verify_c_sources(&false_contract, &sources)
        .expect_err("returned loop path must still be checked after joining the branch");
}

// The source declares byte and uint64 pointer locals. Invariants must retain
// those types even though neither local exists at function entry.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_09")]
fn loop_local_pointer_invariants_retain_declared_element_types() {
    let (click, sources) = loop_fixture("loop_local_pointer_element_types");
    verify_c_sources(&click, &borrowed_sources(&sources)).unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: local pointer bounds mutation and expansion"]
fn loop_local_pointer_invariants_refuse_short_wide_views_and_expand() {
    let (click, sources) = loop_fixture("loop_local_pointer_element_types");
    let sources = borrowed_sources(&sources);
    let wide_start = click.find("int32 wide(").unwrap();
    let (byte, wide) = click.split_at(wide_start);
    let forged = format!(
        "{byte}{}",
        wide.replacen(
            "invariant viewable(chunk[0..4]);",
            "invariant viewable(chunk[0..8]);",
            1
        )
    );
    let error = verify_c_sources(&forged, &sources).unwrap_err();
    assert!(
        error.message().contains("loop 0 invariant 0 entry"),
        "{error:?}"
    );
    let forged_frame = format!(
        "{byte}{}",
        wide.replacen("views chunk[0..4];", "views chunk[0..8];", 1)
    );
    let error = verify_c_sources(&forged_frame, &sources).unwrap_err();
    assert!(
        error
            .message()
            .contains("loop declares a resource the enclosing function does not hold"),
        "{error:?}"
    );
    for function in ["f", "wide"] {
        let expanded = expand_function_proof_source(&click, &sources, function).unwrap();
        verify_c_sources(&expanded, &sources).unwrap();
    }
}

// Distinct-block view rewrites already work. Frontend byte pointers use a
// shared external block, so this catches the offset-equality representation.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_09")]
fn byte_pointer_view_aliases_rewrite_readable_addresses() {
    let (click, sources) = loop_fixture("byte_pointer_view_alias_rewrite");
    verify_c_sources(&click, &borrowed_sources(&sources)).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_09")]
fn native_read_aliases_do_not_supply_missing_authority_or_bounds() {
    let (click, sources) = loop_fixture("native_read_retains_wide_index_beside_narrow_alias");
    let sources = borrowed_sources(&sources);
    for invalid in [
        click.replace(
            "views base[0u64..held];",
            "requires viewable(cursor[0u64..1u64]);",
        ),
        click.replace("requires cursor == base + (held - remaining);", ""),
        click.replace("requires 1u64 <= remaining;", "requires 0u64 <= remaining;"),
        click.replace("requires remaining <= held;", ""),
    ] {
        assert_ne!(invalid, click);
        verify_c_sources(&invalid, &sources).expect_err(
            "a pointer equality or pure viewability cannot authorize an unchecked read",
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: native read alias expansion"]
fn native_read_aliases_expand_and_reverify() {
    let (click, sources) = loop_fixture("native_read_retains_wide_index_beside_narrow_alias");
    let sources = borrowed_sources(&sources);
    let expanded = expand_function_proof_source(&click, &sources, "read").unwrap();
    verify_c_sources(&expanded, &sources).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_09")]
fn theorem_application_expands_with_a_recorded_historical_byte_premise() {
    let (click, sources) = loop_fixture("theorem_application_reuses_recorded_historical_premise");
    let sources = borrowed_sources(&sources);
    let expanded = expand_function_proof_source(&click, &sources, "f").unwrap();
    assert!(
        expanded.contains("have p[0] == old(p)[index] by {"),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(same_byte(p[0], old(p)[index]));"),
        "{expanded}"
    );
    verify_c_sources(&expanded, &sources).unwrap();
    let missing = expanded.replace("requires index == 0;", "");
    verify_c_sources(&missing, &sources)
        .expect_err("retaining a source spelling cannot supply its missing premise");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: readable pointer alias mutations and expansion"]
fn byte_pointer_view_alias_rewrites_refuse_missing_authority_and_expand() {
    let (click, sources) = loop_fixture("byte_pointer_view_alias_rewrite");
    let sources = borrowed_sources(&sources);
    for forged in [
        click.replace("requires cursor == bytes;", ""),
        click.replace("views bytes[0..4];", ""),
        click.replacen("viewable(cursor[0..4])", "viewable(cursor[0..8])", 1),
    ] {
        assert!(verify_c_sources(&forged, &sources).is_err());
    }
    for function in ["f", "shifted"] {
        let expanded = expand_function_proof_source(&click, &sources, function).unwrap();
        verify_c_sources(&expanded, &sources).unwrap();
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: pointer cursor invariant expansion and cold replay"]
fn pointer_cursor_invariant_expands_and_replays() {
    let (click, sources) = loop_fixture("pointer_cursor_loop_expansion");
    let sources = borrowed_sources(&sources);
    verify_c_sources(&click, &sources).unwrap();
    let expanded = expand_function_proof_source(&click, &sources, "f").unwrap();
    assert!(!expanded.contains("transport("), "{expanded}");
    assert!(expanded.matches("normalize()").count() <= 4, "{expanded}");
    for law in ["product_lower_bound", "product_upper_bound"] {
        assert!(
            expanded
                .matches(&format!("apply(click::integer::{law}("))
                .count()
                >= 4,
            "{expanded}"
        );
    }
    without_implicit_solve_for_claim("f.contract", || {
        verify_c_sources(&expanded, &sources).map_err(|error| error.report())
    })
    .unwrap();
}

// Loop resource selection must use the same checked pointer-alias graph as
// calls; an abstract outer cursor is not the input's syntactic block.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn nested_loop_cursor_alias_retains_enclosing_input_view() {
    let (click, sources) = loop_fixture("nested_loop_cursor_view_authority");
    verify_c_sources(&click, &borrowed_sources(&sources)).unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: nested cursor authority mutations and expansion"]
fn nested_loop_cursor_views_refuse_forged_ranges_and_expand() {
    let (click, sources) = loop_fixture("nested_loop_cursor_view_authority");
    let sources = borrowed_sources(&sources);
    for forged in [
        click.replacen("views bytes[0..8];", "", 1),
        click.replace("views chunk[0..4];", "views chunk[0..8];"),
        click.replace(
            "invariant cursor == bytes + (4 * outer);",
            "invariant cursor == bytes + (4 * outer + 1);",
        ),
    ] {
        assert!(verify_c_sources(&forged, &sources).is_err());
    }
    let expanded = expand_function_proof_source(&click, &sources, "f").unwrap();
    assert!(!expanded.contains("transport("), "{expanded}");
    without_implicit_solve_for_claim("f.contract", || {
        verify_c_sources(&expanded, &sources).map_err(|error| error.report())
    })
    .unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_10")]
fn a_loop_state_is_one_entry_under_every_spelling() {
    let exit = |region| ProgramPointRef {
        region,
        kind: ProgramPointKind::Exit,
    };
    let state = ExecutionState::new();
    let mut retained_states = RecordedStates::new();
    // Recorded before the proof labels the loop: the label adopts the entry.
    retained_states.insert(exit(CodeRegionRef::Loop(0)), state.clone());
    retained_states.label_loop(0, "outer");
    retained_states.label_loop(0, "also_outer");
    retained_states.insert(exit(CodeRegionRef::Loop(1)), state.clone());
    for spelling in [
        CodeRegionRef::Loop(0),
        CodeRegionRef::Label("outer".to_string()),
        CodeRegionRef::Label("also_outer".to_string()),
    ] {
        assert!(retained_states.contains_key(&exit(spelling)));
    }
    let keys = retained_states
        .iter()
        .map(|(selector, _)| selector.clone())
        .collect::<Vec<_>>();
    assert_eq!(
        keys,
        [
            ProgramPointSelector::ProgramPoint(exit(CodeRegionRef::Loop(1))),
            ProgramPointSelector::ProgramPoint(exit(CodeRegionRef::Label("outer".to_string()))),
        ],
        "each point is one entry, spelled by its loop's first label"
    );
    assert!(!retained_states.contains_key(&exit(CodeRegionRef::Label("inner".to_string()))));
}

/// Recorded states find the point whose memory reads given bytes: each
/// recorded memory answers with its own point, a newer point recording the
/// same bytes takes over, and a removed point no longer answers.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_10")]
fn recorded_states_find_the_point_reading_a_memory() {
    let mark = |name: &str| ProgramPointSelector::Mark(name.to_string());
    let memory = |index: u32| {
        let pointer = Address::symbolic(Variable(97_400 + u64::from(index)));
        crate::kernel::intern_memory(
            SymbolicMemory::new().store(pointer, ProgramValue::Int32(MachineTerm::constant(index))),
        )
    };
    let state = |memory: &crate::kernel::SharedMemory| {
        ExecutionState::new().with_memory(memory.memory().clone())
    };
    let mut retained_states = RecordedStates::new();
    let memories = (0..8).map(memory).collect::<Vec<_>>();
    for (index, memory) in memories.iter().enumerate() {
        retained_states.insert(mark(&format!("m{index}")), state(memory));
    }
    for (index, memory) in memories.iter().enumerate() {
        let (selector, _) = retained_states
            .point_reading_memory(memory)
            .expect("every recorded memory has a point");
        assert_eq!(*selector, mark(&format!("m{index}")));
    }
    retained_states.insert(mark("again"), state(&memories[3]));
    assert_eq!(
        retained_states
            .point_reading_memory(&memories[3])
            .map(|(selector, _)| selector.clone()),
        Some(mark("again"))
    );
    retained_states.remove(&mark("again"));
    assert_ne!(
        retained_states
            .point_reading_memory(&memories[3])
            .map(|(selector, _)| selector.clone()),
        Some(mark("again"))
    );
    assert!(retained_states.point_reading_memory(&memory(100)).is_none());
}

/// The indexed clause list binds, orders and answers label, scope and
/// rebinding questions exactly as the whole-list fold and walks it
/// replaced, over a long sequence of binds that rebind loops, move labels
/// between loops and change scopes.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by loop_batch_10")]
fn indexed_structural_clauses_agree_with_the_clause_list_walks() {
    let parsed = parse(
        r#"
        verifying "count.c";
        int32 count(int32 i) { ensures result >= 0; } by {
            loop a { invariant i >= 0; }
            loop b { invariant i >= 0; }
            loop { invariant i >= bound; }
        }
    "#,
    )
    .unwrap();
    let function = &parsed.function_blocks()[0];
    let templates = function
        .grouped_proof()
        .unwrap()
        .tactics()
        .unwrap()
        .iter()
        .map(|tactic| match tactic {
            ProofTactic::Loop(template) => template.clone(),
            _ => panic!("expected loop templates"),
        })
        .collect::<Vec<_>>();
    let value = |n| ContractExpression::ProgramExpression(ProgramExpression::Value(int32(n)));
    let scoped = templates[2].with_scope(BTreeMap::from([("bound".to_string(), value(0))]));
    let choices = [&templates[0], &templates[1], &templates[2], &scoped];
    // The fold `with_bound_frontier_loop_clauses` made over a `Vec`.
    let fold = |list: &[StructuralClause], clause: StructuralClause| {
        let mut list = list.to_vec();
        match list.iter().position(|existing| {
            matches!(existing.region(), CodeRegion::Loop(_)) && existing.region() == clause.region()
        }) {
            Some(position) => list[position] = clause,
            None => list.push(clause),
        }
        list
    };
    let mut block = function.clone();
    let mut reference = Vec::<StructuralClause>::new();
    let mut seed = 7u64;
    for _ in 0..300 {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let template = choices[(seed >> 33) as usize % choices.len()];
        let loop_index = (seed >> 40) as usize % 7;
        let clause = template.bound_to_loop(loop_index);
        reference = fold(&reference, clause.clone());
        block = block.with_bound_frontier_loop_clauses(&[clause]);
        let clauses = block.structural_clauses();
        assert_eq!(clauses.to_vec(), reference);
        for label in ["a", "b", "c"] {
            assert_eq!(
                clauses.labelled_region(label),
                reference
                    .iter()
                    .find(|clause| clause.label() == Some(label))
                    .map(|clause| clause.region()),
                "label {label}"
            );
        }
        let mut regions = BTreeMap::<&str, &CodeRegion>::new();
        let rebound = reference.iter().any(|clause| {
            clause.label().is_some_and(|label| {
                regions
                    .insert(label, clause.region())
                    .is_some_and(|previous| previous != clause.region())
            })
        });
        assert_eq!(clauses.has_rebound_label(), rebound);
        assert_eq!(
            clauses.any_scoped(),
            reference.iter().any(|clause| !clause.scope.is_empty())
        );
        assert_eq!(
            clauses.any_scoped_or_resourced(),
            reference
                .iter()
                .any(|clause| !clause.scope.is_empty() || !clause.resources().is_empty())
        );
        // A check that refuses loops past a bound finds the first refused
        // clause whether or not earlier clauses were checked before.
        let loop_count = 1 + (seed >> 50) as usize % 7;
        let check = |clause: &StructuralClause| match clause.region() {
            CodeRegion::Loop(index) if *index >= loop_count => Err(*index),
            _ => Ok(()),
        };
        let expected = reference.iter().try_for_each(check);
        assert_eq!(
            block.validate_structural_clauses(loop_count, check),
            expected
        );
    }
}

#[cfg(feature = "fast-gate")]
test_batches! {
    file: "loop_tests.rs",
    marker: "loop_batch_",
    loop_batch_00: [
        loop_metadata_sees_address_escape_after_the_loop,
        nested_conjunction_extraction_precedes_explicit_arithmetic_steps,
        lexicographic_ranking_bundle_prints_its_pivot_arm,
        smart_ranking_closure_expands_its_pivot_arm,
        separately_declared_guarded_invariants_close_at_the_back_edge,
    ],
    loop_batch_01: [
        smart_ranking_closure_reads_an_inequality_in_scope,
        migrated_negative_loop_fixtures_reach_the_decrease_check,
        loop_preservation_have_resolves_entry_label_and_expands,
        grouped_arithmetic_using_expands_to_checked_certificate,
    ],
    loop_batch_02: [
        symbolic_alignment_expands_to_ordinary_proof_and_rechecks_without_planning,
        explicit_straight_line_swap_preserves_an_entry_bound,
        frontier_local_loop_verifies_and_advances_to_exit,
        individual_loop_proof_has_no_whole_claim_acceptance_check,
    ],
    loop_batch_03: [
        loop_initialization_theorem_search_retains_checked_fixed_state_proof,
        loop_initialization_solve_retains_checked_fixed_state_proof,
        frontier_local_loop_rejects_a_non_loop_frontier,
        frontier_loop_initialization_rejects_execution_tactics,
    ],
    loop_batch_04: [
        frontier_loop_preservation_reports_a_rest_that_does_not_run,
        frontier_local_loop_verifies_a_lowered_c_for_loop,
        frontier_local_loop_verifies_at_a_branch_local_frontier,
        frontier_loop_binding_replaces_scope_without_merging_declarations,
    ],
    loop_batch_05: [
        frontier_loop_step_expansion_uses_the_current_invariant_lowering,
        frontier_local_loop_checks_an_optional_decreases_measure,
        frontier_local_loop_keyword_expands_omitted_phases,
        loop_exit_solve_expands_invariant_conjuncts_explicitly,
    ],
    loop_batch_06: [
        frontier_local_loop_does_not_leak_phase_tactics_into_a_later_expansion,
        frontier_local_loop_expands_an_explicit_nested_tactic_at_its_own_location,
        frontier_local_loop_at_function_entry_keeps_initialization_capture_separate,
        frontier_local_loop_expands_a_tactic_inside_preservation_at_its_own_location,
    ],
    loop_batch_07: [
        explicit_loop_closer_cannot_bypass_proof_owned_bundle_check,
        body_final_branch_preservation_completes_at_typed_back_edge_boundary,
        frontier_local_loop_exit_bound_weakens_to_a_looser_ensures,
        whole_claim_expansion_reconstructs_nested_decided_branch_and_loop_match,
    ],
    loop_batch_08: [
        changed_break_exit_does_not_label_head_invariants_as_exit_facts,
        conditional_loop_resources_parse_print_and_resolve_scope,
        conditional_loop_resources_reject_unsupported_binding_and_body_items,
        loop_return_closers_do_not_require_distinct_result_values,
    ],
    loop_batch_09: [
        loop_local_pointer_invariants_retain_declared_element_types,
        byte_pointer_view_aliases_rewrite_readable_addresses,
        native_read_aliases_do_not_supply_missing_authority_or_bounds,
        theorem_application_expands_with_a_recorded_historical_byte_premise,
    ],
    loop_batch_10: [
        a_loop_state_is_one_entry_under_every_spelling,
        recorded_states_find_the_point_reading_a_memory,
        indexed_structural_clauses_agree_with_the_clause_list_walks,
    ],
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s focused, expansion and false-result control"]
fn shared_post_test_after_switch_continue_expands_and_rejects_a_false_result() {
    let (click, sources) = loop_fixture("do_while_switch_continue");
    let sources = borrowed_sources(&sources);
    let checked = verify_c_sources(&click, &sources).expect("shared post-test verifies");
    let expanded =
        expand_checked_grouped_claim(&click, &checked, "do_while_switch_continue_rejected")
            .expect("shared post-test expands");
    verify_c_sources(&expanded, &sources).expect("expanded post-test verifies");
    let mut false_claim = click.clone();
    let at = false_claim.rfind("ensures result == 0;").unwrap();
    false_claim.replace_range(
        at..at + "ensures result == 0;".len(),
        "ensures result == 1;",
    );
    assert!(verify_c_sources(&false_claim, &sources).is_err());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.3s focused, expands and rechecks two ranked shared-phase proofs"]
fn shared_test_and_update_ranking_expands_and_rechecks() {
    let (click, sources) = loop_fixture("shared_loop_test_and_update");
    let sources = borrowed_sources(&sources);
    let checked = verify_c_sources(&click, &sources).expect("ranked shared phases verify");
    for function in ["shared_for", "shared_do"] {
        let expanded = expand_checked_grouped_claim(&click, &checked, function)
            .expect("ranked shared phases expand");
        verify_c_sources(&expanded, &sources).expect("expanded ranked shared phases verify");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s focused, live and expired inline-reader storage controls"]
fn shared_post_test_scope_retires_storage_after_a_switch_continue() {
    let (click, sources) = loop_fixture("shared_loop_post_test_ends_body_scope");
    let sources = borrowed_sources(&sources);
    let live = click.split("int32 expired_post_test()").next().unwrap();
    verify_c_sources(live, &sources).expect("the inline reader accepts live local storage");
    let error = verify_c_sources(&click, &sources).expect_err("the expired array is refused");
    assert!(
        error.message().contains("invalid memory access"),
        "{}",
        error.message()
    );
}
