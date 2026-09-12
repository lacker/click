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
fn expanded_loop_phase_proofs_are_certificates() {
    for (filename, function) in [
        // Automatically planned initialization and preservation.
        ("count_to_n_loop_invariant", "count_to_n_loop_invariant"),
        // A source `close_invariants()` inside an explicit `preserve by`.
        ("c_decreases_count_up", "count_to_n"),
        // An explicit `close_invariants by` body.
        ("loop_invariant_body", "count"),
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
        let parsed = crate::surface::parse(&expanded)
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
    assert!(
        expanded.contains("arithmetic_certificate signed_int32"),
        "{expanded}"
    );
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

/// The lexicographic pivot is an arm choice, not a kernel search. Only the
/// second component decreases on the `j > 0` path and only the first on the
/// other, so the expansion must print `right()` on one path and `left()` on
/// the other, the expansion must reverify through the ordinary entry point,
/// and swapping either arm must be rejected.
#[test]
fn lexicographic_ranking_bundle_prints_and_pins_its_pivot_arm() {
    let (click, sources) = loop_fixture("c_decreases_lexicographic_loop");
    let sources = borrowed_sources(&sources);
    let expanded = expand_c0_claim_source(&click, &sources, "phase_count", CProofClaim::Grouped)
        .unwrap_or_else(|error| panic!("lexicographic expansion failed: {}", error.message()));
    let closer = expanded
        .find("close_invariants by {")
        .expect("the expansion keeps an explicit bundle closer");
    let closers = &expanded[closer..];
    assert!(
        closers.contains("right();"),
        "the second-component pivot must be printed: {expanded}"
    );
    assert!(
        closers.contains("left();"),
        "the first-component pivot must be printed: {expanded}"
    );
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!(
            "the expanded lexicographic proof must reverify: {}\n{expanded}",
            error.message()
        )
    });

    let wrong_first = expanded.replacen("right();", "left();", 1);
    assert_ne!(wrong_first, expanded);
    verify_c0_sources(&wrong_first, &sources)
        .expect_err("the other pivot arm must be rejected on the `j > 0` path");

    let last_left = expanded
        .rfind("left();")
        .expect("a printed first-component arm");
    let mut wrong_last = expanded.clone();
    wrong_last.replace_range(last_left..last_left + "left();".len(), "right();");
    verify_c0_sources(&wrong_last, &sources)
        .expect_err("the other pivot arm must be rejected on the second path");
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
    assert_eq!(
        arithmetic_certificate_premises(closer).len(),
        2,
        "both ranking members must be closed by one signed certificate: {expanded}"
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
        expanded.contains("left();"),
        "the chosen pivot arm must be printed: {expanded}"
    );
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!(
            "the expanded nested-loop proof must reverify: {}\n{expanded}",
            error.message()
        )
    });
    let wrong_arm = expanded.replacen("left();", "right();", 1);
    assert_ne!(wrong_arm, expanded);
    verify_c0_sources(&wrong_arm, &sources)
        .expect_err("the other pivot arm must be rejected on this back edge");
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
        if error.message().contains("kernel goal") {
            assert!(error.message().contains("recent premises"));
        }
    }
}

#[test]
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
        expanded.contains("arithmetic_certificate special"),
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
fn symbolic_alignment_expands_to_special_certificate_and_rechecks_without_planning() {
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
        "    simp();\n}",
        "    have aligned(p + i, 8) by { simp(); }\n    simp();\n}",
    );
    verify_c0_sources(&click, &sources).unwrap();
    let expanded =
        expand_c0_claim_source(&click, &sources, "element_is_aligned", CProofClaim::Grouped)
            .unwrap();
    assert!(
        expanded.contains("arithmetic_certificate special"),
        "{expanded}"
    );
    let (result, planning) = crate::surface::proof::count_planning_statement_transitions(|| {
        verify_c0_sources(&expanded, &sources)
    });
    result.unwrap();
    assert_eq!(planning, 0, "explicit Special recheck must not plan");
}

#[test]
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

/// The saved expansion checks all invariant bodies without repeating smart
/// search or invoking legacy invariant discovery.
#[test]
fn sorting_rewritten_invariant_body_checks_and_expands() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/bubble_sort3_two_pass_sorted.md");
    let source = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let click = fixture.click_source.as_deref().unwrap();
    assert!(!click.contains("simp("));
    assert!(!click.contains("by simp"));
    assert!(!click.contains("close_invariants();"));
    assert_eq!(click.matches("close_invariants by {").count(), 4);
    verify_c0_sources(click, &sources).unwrap_or_else(|e| panic!("{}", e.message()));
    let expanded = expand_c0_claim_source(
        click,
        &sources,
        "bubble_sort3_two_pass",
        CProofClaim::Grouped,
    )
    .unwrap_or_else(|e| panic!("{}", e.message()));
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|e| panic!("{}", e.message()));
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
#[test]
fn explicit_swap_loop_transports_both_entry_bounds_and_expands() {
    let c = "int32 swap(int32 p[3]) { int32 j; int32 tmp; j = 0; while (j < 1) { if (p[j + 1] < p[j]) { tmp = p[j]; p[j] = p[j + 1]; p[j + 1] = tmp; } j = j + 1; } return 0; }";
    let transport = r#"
        transport(at(before_swap, p[1] <= p[2]), p[0] <= p[2]) using {
            at(before_swap, p[1] <= p[2]); at(before_swap, j) == 0;
        }
        transport(at(before_swap, p[0] <= p[2]), p[1] <= p[2]) using {
            at(before_swap, p[0] <= p[2]); at(before_swap, j) == 0;
        }
    "#;
    let click = format!(
        r#"
        verifying "swap.c";
        int32 swap(int32 p[3]) {{
            requires p[0] <= p[2]; requires p[1] <= p[2];
            consumes p[0..3]; ensures result == 0;
        }} by {{
            step(); step(); step();
            loop {{
                invariant j >= 0 and j <= 1;
                invariant p[0] <= p[2];
                invariant p[1] <= p[2];
                initialize by simp;
                preserve by {{
                    have j == 0 by {{
                        apply(int32_lt_successor_implies_le(j, 0)) using {{ j < 1; }}
                        apply(int32_le_and_not_lt_implies_eq(j, 0)) using {{ j <= 0; j >= 0; }}
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
    let sources = [("swap.c", c)];
    verify_c0_sources(&click, &sources).unwrap_or_else(|e| panic!("{}", e.message()));
    let expanded = expand_c0_claim_source(&click, &sources, "swap", CProofClaim::Grouped)
        .unwrap_or_else(|e| panic!("{}", e.message()));
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|e| panic!("{}", e.message()));
    assert!(!expanded.contains("close_invariants();"));

    let missing_transports = click.replace(transport, "");
    assert_ne!(missing_transports, click);
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

#[test]
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

            int32 initialize_with_theorem(int32 x) {
                requires x >= 0;
                ensures acceptable(result);
            } by {
                loop {
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

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("initialize_with_theorem.c", c_source)])
    });
    verified.expect("loop initialization theorem search should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim.contains("loop(0).initialize")
                    && name == "generated certificate validation"
        )),
        "the checked initialization Proof must not be independently checked: {events:#?}"
    );

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

            int32 initialize_by_simp(int32 x) {
                requires x >= 0;
                ensures result >= 0;
            } by {
                loop {
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

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("initialize_by_simp.c", c_source)])
    });
    verified.expect("loop initialization simp should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim.contains("loop(0).initialize")
                    && name == "generated certificate validation"
        )),
        "the checked initialization simp must not be independently checked: {events:#?}"
    );

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
    assert!(
        error
            .message()
            .contains("must execute exactly one complete loop-body iteration"),
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
            "the expanded perpetual-loop proof should freshly check: {}\n{expanded}",
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
        expanded.contains("apply(int32_le_and_not_lt_implies_eq("),
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
                        branch {
                            ensuring { fact parity >= 0 and parity <= 1; }
                            then { step(); }
                            else { step(); }
                        }
                        close_invariants();
                    }"#,
    );
    let sources = [("flip_to_n.c", c_source)];
    verify_c0_sources(&explicit, &sources).expect(
        "explicit body-final branch preservation should complete at the typed back-edge boundary",
    );

    let automatic = template.replace("{preserve}", "");
    verify_c0_sources(&automatic, &sources)
        .expect("automatic preservation should plan through the body-final branch to the boundary");

    let broken = automatic.replace(
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
    // `int32_ge_transitive` / `int32_le_transitive`), not only the exact
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
