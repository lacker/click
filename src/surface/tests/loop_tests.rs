use super::*;

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
/// must leave `initialize` and `preserve` bodies that contain no smart tactic,
/// so nothing in them is a leaf `ProofCertificate` refuses. In particular the
/// automatic preservation planner's own closer is expanded before the phase is
/// retained; a bare `close_invariants()` or a trailing `simp()` would be
/// rejected here exactly as `ProofCertificate::from_proof_tactics` rejects it.
#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn expanded_loop_phase_proofs_are_certificates() {
    for (filename, function) in [
        // Automatically planned initialization and preservation.
        ("count_to_n_loop_invariant", "count_to_n_loop_invariant"),
        // A source `close_invariants()` inside an explicit `preserve by`.
        ("c_decreases_count_up", "count_to_n"),
        // An explicit `close_invariants by` body.
        ("loop_invariant_body", "count"),
        // Guarded entry judgments survive more than two declarations.
        ("loop_three_invariant_initialization", "probe_fill"),
        // Different source clauses can share one semantic fact at exit.
        ("loop_semantically_duplicate_invariants", "probe_fill"),
        // Readability certificates name a pointer field through void*.
        ("fork_join_worker_direct_contract", "fill_range"),
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
        let expanded = expand_c0_claim_source(click, &sources, function, CProofClaim::Grouped)
            .unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
        assert!(
            !expanded.contains("close_invariants();"),
            "{filename}: {expanded}"
        );
        let parsed = crate::surface::verification::parse_c0_click_file(&expanded, &sources)
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
                ("preserve", clause.preserve_proof()),
            ] {
                let proof =
                    proof.unwrap_or_else(|| panic!("{filename}: `{phase}` was not expanded"));
                let tactics = proof.tactics().unwrap_or_else(|| {
                    panic!("{filename}: `{phase}` stayed a smart proof: {expanded}")
                });
                ProofCertificate::from_proof_tactics(tactics).unwrap_or_else(|error| {
                    panic!("{filename}: `{phase}` is not a certificate: {error:?}\n{expanded}")
                });
            }
        }
        verify_c0_sources(&expanded, &sources)
            .unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
    }
}

#[test]
fn nested_conjunction_extraction_precedes_explicit_arithmetic_certificate() {
    let (click, sources) = loop_fixture("arithmetic_conjunction_provenance");
    let sources = borrowed_sources(&sources);
    let expanded = expand_c0_claim_source(&click, &sources, "drain", CProofClaim::Grouped)
        .expect("nested conjunction provenance should expand");
    assert!(expanded.contains("extract(n >= 0);"), "{expanded}");
    // The extracted conjunct spells the goal under a mirrored order, which
    // the closers now accept, so the certificate needs no arithmetic step
    // after the extraction.
    assert!(!expanded.contains("arithmetic_certificate"), "{expanded}");
    let (result, planning) = crate::surface::proof::count_planning_statement_transitions(|| {
        verify_c0_sources(&expanded, &sources)
    });
    result.expect("expanded extraction and certificate should recheck");
    assert_eq!(planning, 0, "cold certificate recheck must not plan");

    let tampered_sibling = expanded.replacen(
        "n >= 0 and (n <= 2147483647 and n == n)",
        "n != 0 and (n <= 2147483647 and n == n)",
        1,
    );
    verify_c0_sources(&tampered_sibling, &sources)
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
            verify_c0_sources(&click, &sources).unwrap();
            let trace = accepted_proof_trace(&|_, _| None, &|_, _, _| None, &|_, _, _| false, None)
                .expect("the natural exit must retain an accepted execution path");
            assert!(
                !trace.contains("<no checked simple steps"),
                "{filename}: {trace}"
            );
        });
        let expanded =
            expand_c0_claim_source(&click, &sources, function, CProofClaim::Grouped).unwrap();
        verify_c0_sources(&expanded, &sources).unwrap();
    }
}

#[test]
fn natural_goto_mixed_return_retains_paths_and_expands() {
    let (click, sources) = loop_fixture("natural_goto_forward_exit_and_return");
    let sources = borrowed_sources(&sources);
    with_proof_trace("count_down_or_stop", || {
        verify_c0_sources(&click, &sources).unwrap();
        let trace = accepted_proof_trace(&|_, _| None, &|_, _, _| None, &|_, _, _| false, None)
            .expect("both exits must retain accepted execution paths");
        assert!(!trace.contains("<no checked simple steps"), "{trace}");
    });
    for click in [
        click.clone(),
        click.replace("result == 0 or result == 7", "result == 7 or result == 0"),
    ] {
        let expanded =
            expand_c0_claim_source(&click, &sources, "count_down_or_stop", CProofClaim::Grouped)
                .expect("both checked loop exits must expand");
        assert!(!expanded.contains("if result =="), "{expanded}");
        let (result, planning) =
            crate::surface::proof::count_planning_statement_transitions(|| {
                verify_c0_sources(&expanded, &sources)
            });
        result.unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
        assert_eq!(
            planning, 0,
            "expanded proof must cold recheck without planning"
        );
        let forged = expanded.replacen("result == 7", "result == 8", 1);
        verify_c0_sources(&forged, &sources)
            .expect_err("a false return contract must remain rejected");
    }
}

/// The lexicographic pivot is an arm choice, not a kernel search. Only the
/// second component decreases on the `j > 0` path and only the first on the
/// other, so the expansion proves the arm that holds in a `have`, closes the
/// disjunction by `assumption()`, and reverifies through the ordinary entry
/// point.
#[test]
fn lexicographic_ranking_bundle_prints_its_pivot_arm() {
    let (click, sources) = loop_fixture("c_decreases_lexicographic_loop");
    let sources = borrowed_sources(&sources);
    let expanded = expand_c0_claim_source(&click, &sources, "phase_count", CProofClaim::Grouped)
        .unwrap_or_else(|error| panic!("lexicographic expansion failed: {}", error.message()));
    let closer = expanded
        .find("close_invariants by {")
        .expect("the expansion keeps an explicit bundle closer");
    let closers = &expanded[closer..];
    assert!(
        closers.contains("assumption();"),
        "each pivot is proved in a `have` and closed by `assumption`: {expanded}"
    );
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!(
            "the expanded lexicographic proof must reverify: {}\n{expanded}",
            error.message()
        )
    });
}

/// Every bundle member is separately proved. Dropping the conjunct that
/// closes one member, or exchanging two members' proofs, leaves the bundle
/// open: membership and order are part of the checked judgment, not a
/// convention the closer body may reinterpret.
#[test]
fn ranking_bundle_rejects_a_missing_or_exchanged_member() {
    let (click, sources) = loop_fixture("c_decreases_loop");
    let sources = borrowed_sources(&sources);
    verify_c0_sources(&click, &sources).expect("the fixture verifies as written");

    let complete = "close_invariants by {
                both { arithmetic() using { 0 <= n; } }
                and {
                    both { arithmetic() using { 0 <= n; } }
                    and { arithmetic() using { 0 <= n; } }
                }
            }";
    assert!(click.contains(complete), "fixture closer changed: {click}");

    let missing = click.replace(
        complete,
        "close_invariants by {
                both { arithmetic() using { 0 <= n; } }
                and { arithmetic() using { 0 <= n; } }
            }",
    );
    let error = verify_c0_sources(&missing, &sources)
        .expect_err("a closer that proves one member too few must be rejected");
    assert!(
        error.message().contains("decreases at the back edge"),
        "{}",
        error.message()
    );

    let exchanged = click.replace(
        complete,
        "close_invariants by {
                both { arithmetic() using { 0 <= n; } }
                and {
                    both {
                        both { arithmetic() using { 0 <= n; } }
                        and { arithmetic() using { 0 <= n; } }
                    }
                    and { arithmetic() using { 0 <= n; } }
                }
            }",
    );
    verify_c0_sources(&exchanged, &sources)
        .expect_err("a closer nested against the bundle's own order must be rejected");
}

/// The premise lists of every generated signed certificate printed in
/// `region`, one entry per cited premise, in printed order.
fn arithmetic_certificate_premises(region: &str) -> Vec<Vec<String>> {
    let mut blocks = Vec::new();
    let mut rest = region;
    while let Some(start) = rest.find("arithmetic_certificate signed_int32 {") {
        rest = &rest[start + "arithmetic_certificate signed_int32 {".len()..];
        let end = rest.find('}').expect("an unterminated premise list");
        blocks.push(
            rest[..end]
                .lines()
                .map(str::trim)
                .filter(|line| line.starts_with("premise "))
                .filter_map(|line| line.split_once(": "))
                .map(|(_, proposition)| {
                    proposition
                        .split_once(" => ")
                        .map(|(source, _)| source.trim_end_matches(';').to_string())
                        .unwrap_or_else(|| proposition.trim_end_matches(';').to_string())
                })
                .collect::<Vec<_>>(),
        );
        rest = &rest[end..];
    }
    blocks
}

/// A bare `close_invariants()` closes the ranking members the loop's
/// `decreases` clause adds to the bundle, and the smart success expands into
/// the explicit operations that produced it: a `both` per bundle member and
/// one checked signed certificate per arithmetic member. The printed source
/// must reverify through the ordinary entry point without replanning.
#[test]
fn smart_ranking_closure_expands_to_explicit_bundle_members() {
    let (click, sources) = loop_fixture("c_decreases_count_up");
    let sources = borrowed_sources(&sources);
    assert!(
        click.contains("close_invariants();"),
        "the fixture must exercise the smart closer: {click}"
    );
    let expanded = expand_c0_claim_source(&click, &sources, "count_to_n", CProofClaim::Grouped)
        .unwrap_or_else(|error| panic!("count-up expansion failed: {}", error.message()));
    let closer = expanded
        .find("close_invariants by {")
        .expect("the expansion spells the bundle closer");
    let closer = &expanded[closer..];
    assert!(
        !closer.contains("close_invariants();") && !closer.contains("simp();"),
        "the expanded closer must contain no smart leaf: {expanded}"
    );
    assert!(
        closer.contains("both {"),
        "the expanded closer must split the bundle conjunction: {expanded}"
    );
    // The two ranking members and both invariants. `i <= n` closes since
    // `i < n` and `n <= 2147483647` together bound `i + 1`; it needed a lemma
    // application while the planner bounded each atom only by premises naming
    // it alone. `i >= 0` is `i + 1 >= 0` at the back edge; it needed
    // `normalize` while the planner read no `>=` goal over an operation.
    assert_eq!(
        arithmetic_certificate_premises(closer).len(),
        4,
        "both ranking members and both invariants must be closed by one signed certificate each: {expanded}"
    );
    let (result, planning) = crate::surface::proof::count_planning_statement_transitions(|| {
        verify_c0_sources(&expanded, &sources)
    });
    result.unwrap_or_else(|error| {
        panic!(
            "the expanded count-up proof must reverify: {}\n{expanded}",
            error.message()
        )
    });
    assert_eq!(planning, 0, "explicit certificates must not replan");
}

/// A tuple measure's decrease member is a disjunction over pivots, so the
/// smart closer's expansion prints the arm it chose, and that arm is checked
/// like any other: replacing it with the other arm is rejected.
#[test]
fn smart_ranking_closure_expands_its_pivot_arm() {
    let (click, sources) = loop_fixture("c_decreases_nested_loop");
    let sources = borrowed_sources(&sources);
    assert!(
        click.contains("close_invariants by { simp(); }"),
        "the fixture must exercise the smart closer: {click}"
    );
    let expanded = expand_c0_claim_source(&click, &sources, "nested_count", CProofClaim::Grouped)
        .unwrap_or_else(|error| panic!("nested-loop expansion failed: {}", error.message()));
    assert!(
        expanded.contains("assumption();"),
        "the chosen pivot arm must be printed: {expanded}"
    );
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!(
            "the expanded nested-loop proof must reverify: {}\n{expanded}",
            error.message()
        )
    });
}

/// The closer's arithmetic candidates cite a named premise set: the loop
/// head's declared invariants and guard, re-read at iteration entry, and the
/// function's written preconditions. Nothing is selected from the fact
/// context, so the expansion cites exactly those and no other proposition.
#[test]
fn smart_ranking_closure_cites_only_loop_head_and_contract_premises() {
    let (click, sources) = loop_fixture("c_decreases_count_up");
    let sources = borrowed_sources(&sources);
    let expanded = expand_c0_claim_source(&click, &sources, "count_to_n", CProofClaim::Grouped)
        .unwrap_or_else(|error| panic!("count-up expansion failed: {}", error.message()));
    let closer = expanded
        .find("close_invariants by {")
        .expect("the expansion spells the bundle closer");
    let named = [
        // `invariant i >= 0` and `invariant i <= n` at iteration entry.
        "at(statement(3).entry, i) >= at(statement(3).entry, 0)",
        "at(statement(3).entry, i) <= at(statement(3).entry, n)",
        // The loop guard at iteration entry.
        "at(statement(3).entry, i) < at(statement(3).entry, n)",
        // The two conjuncts of the written `requires`.
        "n >= 0",
        "n <= 2147483647",
    ];
    let blocks = arithmetic_certificate_premises(&expanded[closer..]);
    assert!(!blocks.is_empty(), "no cited arithmetic step: {expanded}");
    for premises in blocks {
        for premise in premises {
            assert!(
                named.contains(&premise.as_str()),
                "`{premise}` is not named by the loop head or the contract: {expanded}"
            );
        }
    }
}

/// An inequality that is in scope but is neither a declared invariant, the
/// loop guard, nor a written precondition is not a candidate premise. The
/// nested fixture's outer measure needs `j <= m` at the back edge, which the
/// inner loop's exit makes ambient; dropping the outer `invariant j <= m`
/// leaves the same fact available and must still fail promptly at that
/// member rather than succeed by scanning for it.
#[test]
fn smart_ranking_closure_does_not_scan_for_an_unnamed_ambient_inequality() {
    let (click, sources) = loop_fixture("c_decreases_nested_loop");
    let sources = borrowed_sources(&sources);
    verify_c0_sources(&click, &sources).expect("the fixture verifies as written");
    let weakened = click.replacen(
        "        invariant j <= m;\n        initialize",
        "        initialize",
        1,
    );
    assert_ne!(weakened, click, "the outer invariant was not removed");
    let error = verify_c0_sources(&weakened, &sources)
        .expect_err("an unnamed ambient inequality must not close a ranking member");
    assert!(
        error.message().contains("`0 <= m - j` at the back edge"),
        "{}",
        error.message()
    );
}

#[test]
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
        let error = verify_c0_sources(fixture.click_source.as_deref().unwrap(), &sources)
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
        assert!(!error.message().contains("CMemory {"));
        assert!(!error.message().contains("CState {"));
        if error.message().contains("goal:") {
            assert!(error.message().contains("recent premises"));
        }
    }
}

#[test]
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
        verify_c0_sources(click, &sources)
            .unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
        let expanded = expand_c0_claim_source(click, &sources, function, CProofClaim::Grouped)
            .unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
        assert!(!expanded.contains("close_invariants();"), "{filename}");
        assert!(expanded.contains("close_invariants by {"), "{filename}");
        verify_c0_sources(&expanded, &sources)
            .unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
    }
}

#[test]
fn loop_preservation_have_resolves_entry_label_and_expands() {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests/loop_entry_snapshot.md");
    let source = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let click = fixture.click_source.unwrap();
    verify_c0_sources(&click, &sources).unwrap_or_else(|e| panic!("{}", e.message()));
    let expanded = expand_c0_claim_source(&click, &sources, "drain_to_zero", CProofClaim::Grouped)
        .unwrap_or_else(|e| panic!("{}", e.message()));
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|e| panic!("{}", e.message()));
}

#[test]
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
    verify_c0_sources(&click, &sources).unwrap_or_else(|e| panic!("{}", e.message()));
    let expanded = expand_c0_claim_source(&click, &sources, "last_element", CProofClaim::Grouped)
        .unwrap_or_else(|e| panic!("{}", e.message()));
    assert!(
        expanded.contains("arithmetic_certificate rules"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|e| panic!("{}", e.message()));
}

#[test]
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
    verify_c0_sources(&click, &sources).unwrap();
    let expanded = expand_c0_claim_source(&click, &sources, "bump", CProofClaim::Grouped).unwrap();
    assert!(
        expanded.contains("arithmetic_certificate signed_int32"),
        "{expanded}"
    );
    assert!(!expanded.contains("arithmetic() using"), "{expanded}");
    let (result, planning) = crate::surface::proof::count_planning_statement_transitions(|| {
        verify_c0_sources(&expanded, &sources)
    });
    result.unwrap();
    assert_eq!(planning, 0, "explicit certificate recheck must not plan");
}

#[test]
fn symbolic_alignment_refuses_steps_beyond_the_single_viewed_record() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/aligned_symbolic_displacement.md");
    let source = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let click = fixture.click_source.unwrap();
    // A single record supports only its own position and onepast formation;
    // alignment alone cannot justify the contract's indices two and three.
    let error = verify_c0_sources(&click, &sources).unwrap_err();
    assert!(
        error
            .message()
            .contains("pointer arithmetic left the pointed-to object"),
        "{}",
        error.message()
    );
    assert!(
        error
            .message()
            .contains("return ((unsigned long)(p + i) & 7) == 0;")
    );
}

#[test]
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
        let explicit = fixture
            .click_source
            .unwrap()
            .replace("close_invariants();", "close_invariants by { simp(); }");
        verify_c0_sources(&explicit, &sources)
            .unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
        let expanded = expand_c0_claim_source(&explicit, &sources, function, CProofClaim::Grouped)
            .unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
        assert!(!expanded.contains("close_invariants();"));
        verify_c0_sources(&expanded, &sources)
            .unwrap_or_else(|e| panic!("{filename}: {}", e.message()));
    }
}

#[test]
fn explicit_straight_line_swap_transports_an_entry_bound() {
    for index in ["0", "j"] {
        let c = format!(
            "int32 swap(int32 p[3], int32 j) {{ int32 tmp; tmp = p[{index}]; p[{index}] = p[{index} + 1]; p[{index} + 1] = tmp; return 0; }}"
        );
        let click = r#"
            verifying "swap.c";
            int32 swap(int32 p[3], int32 j) {
                requires j == 0;
                requires p[0] <= p[2];
                requires p[1] <= p[2];
                consumes p[0..3];
                ensures p[0] <= p[2];
            } by {
                step(); step(); step(); step();
                have p[0] <= p[2] by {
                    transport(old(p[1]) <= old(p[2]), p[0] <= p[2]) using {
                        old(p[1]) <= old(p[2]); old(j) == 0;
                    }
                    assumption();
                }
                step(); simp();
            }
        "#;
        verify_c0_sources(click, &[("swap.c", c.as_str())])
            .unwrap_or_else(|e| panic!("index {index}: {}", e.message()));
    }
}

/// A reduction of the second sorting loop, not a replacement for its original C.
/// Existing simple steps suffice when entry index and cell facts are explicit.
fn explicit_swap_loop_fixture(include_transports: bool) -> (&'static str, String) {
    let c = "int32 swap(int32 p[3]) { int32 j; int32 tmp; j = 0; while (j < 1) { if (p[j + 1] < p[j]) { tmp = p[j]; p[j] = p[j + 1]; p[j + 1] = tmp; } j = j + 1; } return 0; }";
    let transport = r#"
        transport(at(before_swap, p[1] <= p[2]), p[0] <= p[2]) using {
            at(before_swap, p[1] <= p[2]); at(before_swap, j) == 0;
        }
        transport(at(before_swap, p[0] <= p[2]), p[1] <= p[2]) using {
            at(before_swap, p[0] <= p[2]); at(before_swap, j) == 0;
        }
    "#;
    let transport = if include_transports { transport } else { "" };
    let click = format!(
        r#"
        verifying "swap.c";
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
                initialize by simp;
                preserve by {{
                    have j == 0 by {{
                        apply(int32_less_than_increment_implies_less_equal(j, 0)) using {{ j < 1; }}
                        apply(int32_less_equal_and_not_less_than_implies_equal(j, 0)) using {{ j <= 0; j >= 0; }}
                        assumption();
                    }}
                    mark before_swap;
                    if p[j + 1] < p[j] {{
                        step(); step(); step(); step(); step();
                        {transport}
                        close_invariants by {{ simp(); }}
                    }} else {{
                        step(); step(); step();
                        close_invariants by {{ simp(); }}
                    }}
                }}
            }}
            step(); simp();
        }}
    "#
    );
    (c, click)
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn explicit_swap_loop_transports_both_entry_bounds_and_expands() {
    let (c, click) = explicit_swap_loop_fixture(true);
    let sources = [("swap.c", c)];
    verify_c0_sources(&click, &sources).unwrap_or_else(|e| panic!("{}", e.message()));
    let expanded = expand_c0_claim_source(&click, &sources, "swap", CProofClaim::Grouped)
        .unwrap_or_else(|e| panic!("{}", e.message()));
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|e| panic!("{}", e.message()));
    assert!(!expanded.contains("close_invariants();"));
}

#[test]
fn explicit_swap_loop_rejects_missing_entry_bound_transports() {
    let (c, missing_transports) = explicit_swap_loop_fixture(false);
    assert!(!missing_transports.contains("transport("));
    let sources = [("swap.c", c)];
    let error = verify_c0_sources(&missing_transports, &sources).unwrap_err();
    assert!(
        error
            .message()
            .contains("closure body did not prove every invariant obligation")
    );
}

#[test]
fn explicit_invariant_body_checks_expands_and_rejects_incomplete_proofs() {
    let c_source = "int32 count() { int32 i; i = 0; while (i < 3) { i = i + 1; } return i; }";
    let source = r#"
        verifying "count.c";
        int32 count() { ensures result == 3; } by {
            step(); step();
            loop {
                decreases 3 - i;
                invariant i >= 0;
                invariant i <= 3;
                initialize by simp;
                preserve by {
                    step();
                    close_invariants by { simp(); }
                }
            }
            step(); simp();
        }
    "#;
    let sources = [("count.c", c_source)];
    verify_c0_sources(source, &sources).expect("the body must prove the exact closure obligations");
    let position =
        expansion::position_at_offset(source, source.find("close_invariants by").unwrap());
    let expanded = expand_c0_tactic_source_at(source, &sources, position.line, position.column)
        .expect("the checked body should expand");
    assert!(expanded.contains("close_invariants by {"), "{expanded}");
    assert!(expanded.contains("both {"), "{expanded}");
    verify_c0_sources(&expanded, &sources).expect("expanded closure body must recheck");
    for replacement in [
        "close_invariants by { }",
        "close_invariants by { assumption(); }",
        "close_invariants by { both { simp(); } and { } }",
        "close_invariants { simp(); }",
        "close_invariants by { simp(); } close_invariants by { simp(); }",
    ] {
        let invalid = source.replace("close_invariants by { simp(); }", replacement);
        assert!(
            verify_c0_sources(&invalid, &sources).is_err(),
            "accepted {replacement}"
        );
    }
    let premature = source.replace(
        "step();\n                    close_invariants by",
        "close_invariants by",
    );
    assert!(verify_c0_sources(&premature, &sources).is_err());
}

/// The smart closer finds a guarded bundle member's proof with direct steps
/// only, and expansion prints exactly those steps: split the bundle, introduce
/// the definedness guard, cite the body's fact, and close the ranking pair.
#[test]
fn guarded_member_closure_expands_to_intro_inside_both() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/close_invariants_closes_a_guarded_member_by_intro.md");
    let source = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let click = fixture.click_source.as_deref().unwrap();
    verify_c0_sources(click, &sources).unwrap_or_else(|error| panic!("{}", error.message()));
    // The `else` arm's closer is the guarded one.
    let offset = click
        .rfind("close_invariants();")
        .expect("the guarded arm closes with the smart closer");
    let position = expansion::position_at_offset(click, offset);
    let expanded = expand_c0_tactic_source_at(click, &sources, position.line, position.column)
        .unwrap_or_else(|error| panic!("{}", error.message()));
    let explicit = expanded[offset..]
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert!(
        explicit.starts_with(
            "close_invariants by { both { intro(); assumption(); } and { assumption(); } }"
        ),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| panic!("{}", error.message()));
}

#[test]
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
    verify_c0_sources(click, &sources).unwrap();
    let expanded =
        expand_c0_claim_source(click, &sources, "bubble_pass3", CProofClaim::Grouped).unwrap();
    assert!(expanded.contains("close_invariants by {"));
    let explicit = expanded.replace("close_invariants();", "close_invariants by { simp(); }");
    verify_c0_sources(&explicit, &sources).unwrap_or_else(|error| panic!("{}", error.message()));
    let expanded =
        expand_c0_claim_source(&explicit, &sources, "bubble_pass3", CProofClaim::Grouped).unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
}

/// The old/current snapshot body verifies and expands on the ordinary stack.
#[test]
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
    verify_c0_sources(click, &sources).unwrap();
    let expanded = expand_c0_claim_source(click, &sources, "copy3", CProofClaim::Grouped).unwrap();
    assert!(expanded.contains("close_invariants by {"));
    let explicit = expanded.replace("close_invariants();", "close_invariants by { simp(); }");
    verify_c0_sources(&explicit, &sources).unwrap_or_else(|error| panic!("{}", error.message()));
    let expanded =
        expand_c0_claim_source(&explicit, &sources, "copy3", CProofClaim::Grouped).unwrap();
    assert!(!expanded.contains("close_invariants();"));
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| panic!("{}", error.message()));
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
                    decreases 3 - i;
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
                loop as count {
                    decreases 3 - i;
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
        }
    "#;
    let sources = [("count_to_three.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
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
        .expect("the compatibility proof should retain expansion provenance");

    let rewritten = expand_c0_claim_source(
        click_source,
        &sources,
        "count_to_three",
        CProofClaim::Ensure(0),
    )
    .expect("the retained individual loop proof should expand");
    verify_c0_sources(&rewritten, &sources)
        .expect("the rewritten individual loop proof should verify normally");
}

#[test]
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
                    unfold(acceptable);
                    simp();
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
                        simp();
                    }
                    preserve by {
                        step();
                        apply(nonnegative_is_acceptable(x));
                        simp();
                    }
                }
                step();
                unfold(acceptable);
                simp();
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("initialize_with_theorem.c", c_source)]);
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
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("initialize_with_theorem.c", c_source)],
        line,
        column,
    )
    .expect("the retained initialization theorem step should expand");
    assert!(
        expanded.contains("apply(nonnegative_is_acceptable(x)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("x >= 0;"), "{expanded}");
    verify_c0_sources(&expanded, &[("initialize_with_theorem.c", c_source)])
        .expect("expanded initialization theorem application should independently verify");
}

#[test]
fn loop_initialization_simp_retains_checked_fixed_state_proof() {
    let c_source = r#"
            int32 initialize_by_simp(int32 x) {
                while (x < 1) {
                    x = 0;
                }
                return x;
            }
        "#;
    let click_source = r#"
            verifying "initialize_by_simp.c";

            int32 initialize_by_simp(int32 x) diverges {
                requires x >= 0;
                ensures result >= 0;
            } by {
                loop diverges {
                    invariant x >= 0;
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

    let verified = verify_c0_sources(click_source, &[("initialize_by_simp.c", c_source)]);
    verified.expect("loop initialization simp should verify through Proof");

    let offset = click_source
        .find("initialize by simp")
        .expect("initialization proof should contain its smart simp")
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
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("initialize_by_simp.c", c_source)],
        line,
        column,
    )
    .expect("the retained initialization closer should expand");
    assert!(!expanded.contains("initialize by simp"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    verify_c0_sources(&expanded, &[("initialize_by_simp.c", c_source)])
        .expect("expanded initialization closer should independently verify");
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
    let message = error.message();
    assert!(
        message.contains("stopped inside the loop body")
            && message.contains("the frontier is at statement")
            && message.contains("still ahead on this path: the body's end"),
        "{message}"
    );
}

#[test]
fn closing_invariants_on_a_break_path_is_refused() {
    let c_source = r#"
            int32 break_once(int32 n) {
                int32 i = n;
                while (i > 0) {
                    break;
                }
                return i;
            }
        "#;
    let click_source = r#"
            verifying "break_once.c";

            int32 break_once(int32 n) {
                requires n >= 0;
                ensures result >= 0;
            } by {
                step();
                step();
                loop {
                    invariant i >= 0;
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

    let error = verify_c0_sources(click_source, &[("break_once.c", c_source)])
        .expect_err("a `break` path has no back edge to close");
    assert!(
        error
            .message()
            .contains("has no back edge on a `break` path"),
        "{}",
        error.message()
    );
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
                    decreases 3 - i;
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
                        decreases 2 - i;
                        invariant i >= 0;
                        invariant i <= 2;
                        initialize by simp;
                        preserve by {
                            step();
                            close_invariants();
                        }
                    }
                    step();
                    simp();
                } else {
                    step();
                    step();
                    step();
                    simp();
                }
            }
        "#;

    verify_c0_sources(click_source, &[("branch_count.c", c_source)])
        .expect("frontier-local loop should use the branch's actual execution context");
}

#[test]
fn frontier_loop_binding_replaces_scope_without_merging_declarations() {
    let parsed = parse(
        r#"
        verifying "count.c";
        int32 count(int32 i) { ensures result >= 0; } by {
            loop {
                invariant i >= bound;
                invariant i >= bound;
                initialize by simp;
                preserve by simp;
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
    let value = |n| ContractExpression::CFragment(CExpression::Value(int32(n)));
    let outer = template.with_scope(BTreeMap::from([("bound".to_string(), value(0))]));
    let inner = template.with_scope(BTreeMap::from([("bound".to_string(), value(1))]));
    let initial = function
        .with_bound_frontier_loop_clauses(&[outer.bound_to_loop(0), outer.bound_to_loop(1)]);
    let rebound = initial.with_frontier_loop_clause(&inner, 1);
    let repeated = rebound.with_bound_frontier_loop_clauses(&[inner.bound_to_loop(1)]);
    assert_eq!(initial.structural_clauses().len(), 2);
    assert_eq!(rebound.structural_clauses(), repeated.structural_clauses());
    assert_eq!(repeated.structural_clauses().len(), 2);
    assert_eq!(repeated.structural_clauses()[0], outer.bound_to_loop(0));
    assert_eq!(repeated.structural_clauses()[1], inner.bound_to_loop(1));
    assert_eq!(repeated.structural_clauses()[1].items().len(), 2);
    assert_eq!(initial.structural_clauses()[1], outer.bound_to_loop(1));
    assert_ne!(
        initial.structural_clauses()[1].resolved().unwrap().items(),
        repeated.structural_clauses()[1].resolved().unwrap().items()
    );
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
                    decreases 2 - i;
                    invariant i >= 0;
                    invariant i <= 2;
                    initialize by simp;
                    preserve by {
                        step();
                        loop {
                            decreases 2 - j;
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

    let sources = [("nested_count.c", c_source)];
    verify_c0_sources(click_source, &sources)
        .expect("nested loop proofs should be scoped to their respective frontiers");
    let expanded =
        expand_c0_claim_source(click_source, &sources, "nested_count", CProofClaim::Grouped)
            .expect("nested loop proofs should expand");
    verify_c0_sources(&expanded, &sources).expect("expanded nested loops should verify");
    let repeated =
        expand_c0_claim_source(&expanded, &sources, "nested_count", CProofClaim::Grouped)
            .expect("expanded nested loops should remain expandable");
    assert_eq!(repeated, expanded);
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
                consumes p[0..n];
                ensures result == n;
            } by {
                step();
                step();
                loop {
                    decreases n - i;
                    invariant i >= 0 and i <= n;
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

    // A bare `step()` is a simple tactic: its expansion is the source.
    assert_eq!(expanded, click_source);
    verify_c0_sources(&expanded, &[("fill_n.c", c_source)])
        .expect("the expanded store should use the invariant at the current frontier");
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
                        have 0 <= n - 1 by {
                            apply(int32_positive_predecessor_is_nonnegative(n)) using { n > 0; }
                        }
                        step();
                        close_invariants by {
                            both { arithmetic() using { 0 <= n; } }
                            and {
                                both { arithmetic() using { 0 <= n; } }
                                and { arithmetic() using { 0 <= n; } }
                            }
                        }
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
                    decreases n - i;
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
            "the expanded frontier-local loop should freshly check: {}\n{expanded}",
            error.message()
        )
    });
}

#[test]
fn loop_exit_simp_expands_invariant_conjuncts_explicitly() {
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
                simp();
            }
        "#;
    let simp_offset = click_source
        .rfind("simp();")
        .expect("proof should contain its final simp");
    let line = click_source[..simp_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = simp_offset
        - click_source[..simp_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("count_to_n.c", c_source)], line, column)
            .expect("loop-exit simp should expand through explicit invariant conjuncts");

    assert!(
        expanded.contains("at(loop(0).exit, i) <= at(loop(0).exit, n);"),
        "{expanded}"
    );
    assert!(
        expanded.contains("not at(loop(0).exit, i) < at(loop(0).exit, n);"),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_less_equal_and_not_less_than_implies_equal("),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("count_to_n.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "the expanded loop-exit proof should freshly check: {}\n{expanded}",
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
                    decreases 3 - i;
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
                    decreases 3 - i;
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
        .expect("expanded explicit initialization tactic should freshly check");
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
                        have 0 <= n - 1 by {
                            apply(int32_positive_predecessor_is_nonnegative(n)) using { n > 0; }
                        }
                        step();
                        close_invariants by {
                            both { arithmetic() using { 0 <= n; } }
                            and {
                                both { arithmetic() using { 0 <= n; } }
                                and { arithmetic() using { 0 <= n; } }
                            }
                        }
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

    // A bare `step()` is a simple tactic: expanding it leaves the source as
    // written, and the loop's other phases stay untouched.
    assert_eq!(expanded, click_source);
    assert!(expanded.contains("initialize by simp"), "{expanded}");
    verify_c0_sources(&expanded, &[("count_to_three.c", c_source)])
        .expect("expanded preservation step should freshly check");
}

#[test]
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

    let error = verify_c0_sources(click_source, &[("overshoot.c", c_source)])
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
                    initialize by simp;
                    {preserve}
                }
                step();
                simp();
            }
        "#;
    let explicit = template.replace(
        "{preserve}",
        r#"preserve by {
                        step();
                        branch ensuring { fact parity >= 0 and parity <= 1; } then { step(); } else { step(); }
                        close_invariants();
                    }"#,
    );
    let sources = [("flip_to_n.c", c_source)];
    verify_c0_sources(&explicit, &sources).expect(
        "explicit body-final branch preservation should complete at the typed back-edge boundary",
    );

    // The omitted-phase planner reaches the same boundary and closes the whole
    // back-edge bundle there, including the two members the `decreases` clause
    // adds. Both arms carry the C branch condition as a named premise, so the
    // ranking members are ordinary arithmetic certificates over the loop head's
    // own clauses.
    let automatic = template.replace("{preserve}", "");
    verify_c0_sources(&automatic, &sources)
        .expect("automatic preservation should plan through the body-final branch to the boundary");

    let broken = template.replace(
        "{preserve}",
        r#"preserve by {
                        step();
                        branch ensuring { fact parity >= 0 and parity <= 1; } then { step(); } else { step(); }
                        close_invariants();
                    }"#,
    );
    let broken = broken.replace(
        "invariant parity >= 0 and parity <= 1;",
        "invariant parity <= 0;",
    );
    let error = verify_c0_sources(&broken, &sources)
        .expect_err("an invariant violated through one body-final arm must fail preservation");
    assert!(
        format!("{error:?}").contains("invariant"),
        "the failure should name the invariant bundle: {error:?}"
    );
}

#[test]
fn frontier_local_loop_exit_bound_weakens_to_a_looser_ensures() {
    // The negated loop guard leaves `i >= 3` at the loop's exit. The checked
    // outcome `simp` must retain a checkable proof of the *looser* bounds
    // `result >= 1` and `result <= 5` (constant-bound weakening through
    // `int32_greater_equal_transitive` / `int32_less_equal_transitive`), not only the exact
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

    verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
        .expect("the checked outcome simp should weaken the loop-exit bound to the looser ensures");
}

#[test]
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
                normalize();
            }
            match marker() {
                Marker::Active => {
                    branch then { step(); } else { step(); }
                    loop {
                        decreases 2 - x;
                        invariant x >= 1;
                        invariant x <= 2;
                        initialize by simp;
                        preserve by {
                            have marker() != Marker::Inactive by {
                                unfold(marker());
                                normalize();
                            }
                            match marker() {
                                Marker::Active => {
                                    step();
                                    close_invariants();
                                },
                                Marker::Inactive => {
                                    contradiction(marker() == Marker::Inactive);
                                },
                            }
                        }
                    }
                    step();
                    simp();
                },
                Marker::Inactive => {
                    contradiction(marker() == Marker::Inactive);
                },
            }
        }
    "#;
    let sources = [("selected_then_loop.c", c_source)];

    verify_c0_sources(click_source, &sources).expect("the reduced source proof should verify");
    let expanded = expand_c0_claim_source(
        click_source,
        &sources,
        "selected_then_loop",
        CProofClaim::Ensure(0),
    )
    .expect("the reduced whole claim should expand");
    verify_c0_sources(&expanded, &sources)
        .expect("the reduced whole-claim expansion should independently verify");
}

#[test]
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
            step(); simp();
        }
    "#;
    for source in [
        source.to_owned(),
        source.replace("invariant 1 == 1;", "invariant 0 == 0;"),
    ] {
        verify_c0_sources(&source, &[("count.c", c)]).unwrap();
        let expanded =
            expand_c0_claim_source(&source, &[("count.c", c)], "count", CProofClaim::Grouped)
                .unwrap();
        verify_c0_sources(&expanded, &[("count.c", c)]).unwrap();
        let false_claim = source.replace("ensures result == n;", "ensures result == n + 1;");
        let error = verify_c0_sources(&false_claim, &[("count.c", c)]).unwrap_err();
        assert!(
            error.message().contains("unclosed goal"),
            "{}",
            error.message()
        );
    }
}

#[test]
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
    verify_c0_sources(&source, &sources).unwrap();
    let expanded =
        expand_c0_claim_source(&source, &sources, "assign_then_break", CProofClaim::Grouped)
            .unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
    for fact in ["r == 0", "at(loop(0).exit, r) == at(loop(0).exit, 0)"] {
        let false_have = source.replace(
            "    step();\n    simp();",
            &format!("    have {fact} by {{ assumption(); }}\n    step();\n    simp();"),
        );
        assert_ne!(source, false_have);
        let error = verify_c0_sources(&false_have, &sources).unwrap_err();
        assert!(
            error.message().contains("`assumption` requires"),
            "{}",
            error.message()
        );
    }
}

#[test]
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
        ContractExpression::CFragment(CExpression::Value(int32(4))),
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
        verify_c0_sources(&click, &sources).unwrap();
        for site in c0_smart_tactic_source_sites(&click, &sources).unwrap() {
            let position =
                c0_tactic_source_position(&click, &sources, &site.claim_label, site.source_index)
                    .unwrap();
            let expanded =
                expand_c0_tactic_source_at(&click, &sources, position.line, position.column)
                    .unwrap_or_else(|error| {
                        panic!("{fixture} {}: {}", site.source_index, error.message())
                    });
            verify_c0_sources(&expanded, &sources).unwrap();
        }
        let expanded =
            expand_c0_claim_source(&click, &sources, function, CProofClaim::Grouped).unwrap();
        assert!(!expanded.contains("if result =="), "{expanded}");
        assert!(
            c0_smart_tactic_source_sites(&expanded, &sources)
                .unwrap()
                .is_empty(),
            "{expanded}"
        );
        let (result, planning) =
            crate::surface::proof::count_planning_statement_transitions(|| {
                verify_c0_sources(&expanded, &sources)
            });
        result.unwrap();
        assert_eq!(
            planning, 0,
            "{fixture}: expanded proof must cold recheck without planning"
        );
    }
}

#[test]
fn nested_loop_return_keeps_the_inner_arms_closer() {
    let c = "int32 f(int32 n) { while (1) { while (1) { return 7; } } }";
    let click = r#"
verifying "nested.c";
int32 f(int32 n) {
    requires n == 5;
    ensures result == 7;
} by {
    loop { decreases 1; invariant n == 5;
        preserve by {
            loop { decreases 1; invariant n == 5;
                preserve by { step(); have result == 7 by simp; simp(); }
            }
        }
    }
}
"#;
    let sources = [("nested.c", c)];
    verify_c0_sources(click, &sources).unwrap();
    let false_arm = click.replace("have result == 7", "have result == 8");
    assert!(
        verify_c0_sources(&false_arm, &sources)
            .unwrap_err()
            .message()
            .contains("could not establish `result == 8`")
    );
    for site in c0_smart_tactic_source_sites(click, &sources).unwrap() {
        let position =
            c0_tactic_source_position(click, &sources, &site.claim_label, site.source_index)
                .unwrap();
        let expanded =
            expand_c0_tactic_source_at(click, &sources, position.line, position.column).unwrap();
        verify_c0_sources(&expanded, &sources).unwrap();
    }
    let expanded = expand_c0_claim_source(click, &sources, "f", CProofClaim::Grouped).unwrap();
    assert!(
        c0_smart_tactic_source_sites(&expanded, &sources)
            .unwrap()
            .is_empty()
    );
    let (result, planning) = crate::surface::proof::count_planning_statement_transitions(|| {
        verify_c0_sources(&expanded, &sources)
    });
    result.unwrap();
    assert_eq!(planning, 0);
}

#[test]
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
    verify_c0_sources(&click, &sources).unwrap();
    let expanded = expand_c0_claim_source(&click, &sources, "f", CProofClaim::Grouped).unwrap();
    assert!(!expanded.contains("if result =="), "{expanded}");
    verify_c0_sources(&expanded, &sources).unwrap();
}

#[test]
fn loop_return_inside_branch_retains_its_fact_ancestry() {
    let c = "int32 f(int32 n) { if (n > 0) { int32 i = 0; while (i < n) { if (i == 2) return 7; i++; } return i; } else { return 7; } }";
    let click = r#"
verifying "branch.c";
int32 f(int32 n) {
    requires n >= 0;
    ensures result == n or result == 7;
} by {
    branch then {
        step(); step();
        loop { decreases n-i; invariant i >= 0; invariant i <= n; }
        step(); have result == n by simp; simp();
    } else { step(); simp(); }
}
"#;
    let sources = [("branch.c", c)];
    verify_c0_sources(click, &sources).unwrap();
    let expanded = expand_c0_claim_source(click, &sources, "f", CProofClaim::Grouped).unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
    let false_contract = click.replace("result == n or result == 7", "result == n");
    verify_c0_sources(&false_contract, &sources)
        .expect_err("returned loop path must still be checked after joining the branch");
}

// The source declares byte and uint64 pointer locals. Invariants must retain
// those types even though neither local exists at function entry.
#[test]
fn loop_local_pointer_invariants_retain_declared_element_types() {
    let (click, sources) = loop_fixture("loop_local_pointer_element_types");
    verify_c0_sources(&click, &borrowed_sources(&sources)).unwrap();
}

#[test]
#[ignore = "nightly: local pointer extent mutation and expansion"]
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
    let error = verify_c0_sources(&forged, &sources).unwrap_err();
    assert!(
        error.message().contains("loop 0 invariant 0 entry"),
        "{error:?}"
    );
    let forged_frame = format!(
        "{byte}{}",
        wide.replacen("views chunk[0..4];", "views chunk[0..8];", 1)
    );
    let error = verify_c0_sources(&forged_frame, &sources).unwrap_err();
    assert!(
        error
            .message()
            .contains("loop declares a resource the enclosing function does not hold"),
        "{error:?}"
    );
    for function in ["f", "wide"] {
        let expanded =
            expand_c0_claim_source(&click, &sources, function, CProofClaim::Grouped).unwrap();
        verify_c0_sources(&expanded, &sources).unwrap();
    }
}

// Distinct-block view rewrites already work. Frontend byte pointers use a
// shared external block, so this catches the offset-equality representation.
#[test]
fn byte_pointer_view_aliases_rewrite_readable_addresses() {
    let (click, sources) = loop_fixture("byte_pointer_view_alias_rewrite");
    verify_c0_sources(&click, &borrowed_sources(&sources)).unwrap();
}

#[test]
#[ignore = "nightly: readable pointer alias mutations and expansion"]
fn byte_pointer_view_alias_rewrites_refuse_missing_authority_and_expand() {
    let (click, sources) = loop_fixture("byte_pointer_view_alias_rewrite");
    let sources = borrowed_sources(&sources);
    for forged in [
        click.replace("requires cursor == bytes;", ""),
        click.replace("views bytes[0..4];", ""),
        click.replacen("viewable(cursor[0..4])", "viewable(cursor[0..8])", 1),
    ] {
        assert!(verify_c0_sources(&forged, &sources).is_err());
    }
    for function in ["f", "shifted"] {
        let expanded =
            expand_c0_claim_source(&click, &sources, function, CProofClaim::Grouped).unwrap();
        verify_c0_sources(&expanded, &sources).unwrap();
    }
}

// Loop resource selection must use the same checked pointer-alias graph as
// calls; an abstract outer cursor is not the input's syntactic block.
#[test]
fn nested_loop_cursor_alias_retains_enclosing_input_view() {
    let (click, sources) = loop_fixture("nested_loop_cursor_view_authority");
    verify_c0_sources(&click, &borrowed_sources(&sources)).unwrap();
}

#[test]
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
        assert!(verify_c0_sources(&forged, &sources).is_err());
    }
    let expanded = expand_c0_claim_source(&click, &sources, "f", CProofClaim::Grouped).unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
}
