use super::*;

const C: &[(&str, &str)] = &[("closing.c", "int32 value(void) { return 7; }")];

fn proof(steps: &str) -> String {
    format!(
        r#"
        verifying "closing.c";
        int32 value() {{ ensures result == 7; }} by {{
            step_until(function.exit);
            {steps}
        }}
    "#
    )
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_closing_batch_00")]
fn explicit_contract_closing_uses_ordinary_known_steps() {
    let source = proof("normalize(); close(); close(); close();");
    let mut verified = without_implicit_solve(|| verify_c_sources(&source, C))
        .unwrap_or_else(|error| panic!("{}", error.message()));
    // Reuse the completed artifact: losing its ordinary root must refuse,
    // rather than admitting a reusable rule through the legacy adapter.
    let function = verified[0].function_block.clone();
    for theorem in &mut verified {
        let mut entry = (**theorem.entry_context.as_ref().unwrap()).clone();
        entry.completion = None;
        theorem.entry_context = Some(std::sync::Arc::new(entry));
    }
    let error = crate::surface::proof::finish_contract_body_root(&function, &verified).unwrap_err();
    assert!(
        error.message().contains("lost its contract root"),
        "{error}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_closing_batch_00")]
fn implicit_contract_closing_expands_into_explicit_steps() {
    let source = proof("close();");
    verify_c_sources(&source, C).unwrap();
    let expanded = expand_function_proof_source(&source, C, "value").unwrap();
    assert!(!expanded.contains("solve();"), "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, C))
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_closing_batch_00")]
fn per_clause_contract_closing_expands_after_its_source_proof() {
    let source = r#"verifying "closing.c";
        int32 value() { ensures result == 7 by { step_until(function.exit); }; }
    "#;
    let expanded = expand_c_claim_source_by_label(source, C, "value.ensures_0").unwrap();
    without_implicit_solve(|| verify_c_sources(&expanded, C))
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_closing_batch_00")]
fn omitted_closing_steps_leave_their_obligations_open() {
    for (count, goal) in [
        (0, "joint returned resources"),
        (1, "allocation lifetime"),
        (2, "write footprint"),
    ] {
        let source = proof(&format!("normalize(); {}", "close(); ".repeat(count)));
        let error = without_implicit_solve(|| verify_c_sources(&source, C))
            .expect_err("ordinary completion cannot supply an omitted proof");
        assert_eq!(
            error.proof_refusal(),
            Some(crate::surface::ProofRefusal::IncompleteProof)
        );
        assert!(
            error
                .message()
                .contains(&format!("outcome still owes contract closing: {goal}")),
            "{error}"
        );
        verify_c_sources(&source, C)
            .expect("the implicit solver supplies the same omitted operations");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_closing_batch_01")]
fn written_solve_closes_only_one_selected_closing_goal() {
    let source = proof("normalize(); close();");
    let error = without_implicit_solve(|| verify_c_sources(&source, C)).unwrap_err();
    assert!(
        error
            .message()
            .contains("outcome still owes contract closing: allocation lifetime"),
        "{error}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_closing_batch_01")]
fn expansion_writes_each_closing_step_and_requires_them_when_cold() {
    let source = proof("normalize();");
    let expanded = expand_function_proof_source(&source, C, "value").unwrap();
    assert_eq!(expanded.matches("close();").count(), 3, "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, C)).unwrap();
    let last = expanded.rfind("close();").unwrap();
    let mut missing = expanded.clone();
    missing.replace_range(last..last + "close();".len(), "");
    let error = without_implicit_solve(|| verify_c_sources(&missing, C)).unwrap_err();
    assert!(
        error
            .message()
            .contains("outcome still owes contract closing: write footprint"),
        "{error}"
    );
}

#[test]
fn expansion_closes_each_rewritten_postcondition() {
    let inputs = [("closing.c", "int32 value(int32 *p) { return *p; }")];
    let source = r#"
        verifying "closing.c";
        int32 value(int32* p) {
            requires p[0] == 7;
            owns p[0];
            ensures result == old(p[0]);
            ensures result == 7;
        } by {
            step_until(function.exit);
            close();
            rewrite(result, old(p[0]));
            close();
            rewrite(result, old(p[0]));
            close();
        }
    "#;
    let claim = "value.contract";
    let expanded = expand_c_claim_source_by_label(source, &inputs, claim).unwrap();
    crate::surface::check_audit_claim(claim, true, || {
        verify_c_sources(&expanded, &inputs).map_err(|error| error.report())
    })
    .unwrap_or_else(|error| panic!("{error}\n{expanded}"));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_closing_batch_01")]
fn proposition_closers_name_the_pending_closing_goal() {
    for closer in [
        "normalize();",
        "close() using {};",
        "all { true => { close(); } true => { close(); } }",
    ] {
        let source = proof(&format!("normalize(); {closer}"));
        let error = verify_c_sources(&source, C).unwrap_err();
        assert!(
            error.message().contains("requires a proposition goal"),
            "{error}"
        );
        assert!(
            error.message().contains("joint returned resources"),
            "{error}"
        );
        assert!(error.message().contains("close()"), "{error}");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_closing_batch_01")]
fn footprint_refusal_names_the_goal_and_the_solver_that_failed() {
    let inputs = [(
        "writes.c",
        "int counter; int write(void) { counter = 9; return 0; }",
    )];
    for (steps, expected) in [
        (
            "normalize();",
            "the implicit solver could not prove the write footprint obligation",
        ),
        (
            "normalize(); close(); close(); close();",
            "this tactic could not prove the write footprint obligation",
        ),
    ] {
        let source = format!(
            r#"verifying "writes.c";
            int32 write() {{ ensures result == 0; }} by {{
                step_until(function.exit); {steps}
            }}"#
        );
        let error = verify_c_sources(&source, &inputs).unwrap_err();
        assert!(error.message().contains(expected), "{error}");
        assert!(
            error.message().contains("outside the mutable footprint"),
            "{error}"
        );
    }
}

fn source_only_clauses(grouped: bool, last_value: i32) -> String {
    let clauses = format!(
        r#"
        ensures result == at(first, x) + 1{};
        ensures at(first, x) == {last_value}{};
    "#,
        if grouped {
            ""
        } else {
            " by { step(); mark first; }"
        },
        if grouped {
            ""
        } else {
            " by { step(); mark first; }"
        }
    );
    format!(
        r#"verifying "source_cells.c";
        int32 set_twice(int32 x) {{ {clauses} }} {}
    "#,
        if grouped {
            "by { step(); mark first; }"
        } else {
            ""
        }
    )
}

const SOURCE_CELLS_C: &[(&str, &str)] = &[(
    "source_cells.c",
    "int32 set_twice(int32 x) { x = 1; x = 2; return x; }",
)];

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_closing_batch_02")]
fn grouped_source_only_claims_complete_and_expand_as_ordinary_proofs() {
    let source = source_only_clauses(true, 1);
    verify_c_sources(&source, SOURCE_CELLS_C).unwrap();
    let expanded = expand_function_proof_source(&source, SOURCE_CELLS_C, "set_twice").unwrap();
    without_implicit_solve(|| verify_c_sources(&expanded, SOURCE_CELLS_C))
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_closing_batch_02")]
fn separate_source_only_clauses_complete_their_own_cells() {
    verify_c_sources(&source_only_clauses(false, 1), SOURCE_CELLS_C).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_closing_batch_02")]
fn proving_one_source_only_clause_cannot_cover_a_false_sibling() {
    for grouped in [false, true] {
        assert!(verify_c_sources(&source_only_clauses(grouped, 9), SOURCE_CELLS_C).is_err());
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_closing_batch_02")]
fn concrete_and_avoided_loops_need_no_summary_measure() {
    let c = [(
        "concrete_exits.c",
        "int32 concrete(int32 n) { while (n > 0) { n = n - 1; } return n; } int32 avoided(int32 n) { if (n < 0) { while (1) {} } return n; }",
    )];
    let source = r#"verifying "concrete_exits.c";
        int32 concrete(int32 n) { requires n == 2; ensures result == 0; }
        int32 avoided(int32 n) { requires n >= 0; ensures result == n; }
    "#;
    verify_c_sources(source, &c).unwrap();
    let expanded = expand_function_proof_source(source, &c, "concrete").unwrap();
    let expanded = expand_function_proof_source(&expanded, &c, "avoided").unwrap();
    without_implicit_solve(|| verify_c_sources(&expanded, &c))
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
fn an_empty_loop_summary_does_not_publish_concrete_exit_evidence() {
    let c = [(
        "concrete_summary.c",
        "int32 summarized(void) { while (1) {} return 0; }",
    )];
    let source = r#"verifying "concrete_summary.c";
        int32 summarized() { ensures result == 0; } by { loop {} }
    "#;
    let error =
        verify_c_sources(source, &c).expect_err("an unranked summary is only partial correctness");
    assert!(
        error.message().contains("loop") && error.message().contains("decreases"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_closing_batch_03")]
fn completed_descent_covers_a_concretely_avoided_recursive_loop() {
    let c = [(
        "retained_descent.c",
        "int32 countdown(int32 n) { if (n > 0) return countdown(n - 1); while (0) { countdown(n); } return 0; }",
    )];
    let source = r#"verifying "retained_descent.c";
        int32 countdown(int32 n) {
            decreases (n, 0);
            requires n >= 0;
            ensures result == 0;
        }
    "#;
    verify_c_sources(source, &c).unwrap();
    let expanded = expand_function_proof_source(source, &c, "countdown").unwrap();
    without_implicit_solve(|| verify_c_sources(&expanded, &c))
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_closing_batch_03")]
fn retained_context_does_not_discharge_an_unproved_recursive_descent() {
    let c = [(
        "unproved_descent.c",
        "int32 countdown(int32 n) { if (n > 0) return countdown(n); return 0; }",
    )];
    let source = r#"verifying "unproved_descent.c";
        int32 countdown(int32 n) {
            decreases (n, 0);
            requires n >= 0;
            ensures result == 0;
        }
    "#;
    assert!(verify_c_sources(source, &c).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_closing_batch_03")]
fn reassigned_numeric_parameter_descent_expands_into_ordinary_steps() {
    let c = [(
        "numeric_descent.c",
        "int32 countdown(int32 n) { if (n > 0) { n = n - 1; return countdown(n); } return 0; }",
    )];
    let source = r#"verifying "numeric_descent.c";
        int32 countdown(int32 n) {
            decreases n;
            requires n >= 0;
            ensures result == 0;
        }
    "#;
    verify_c_sources(source, &c).unwrap();
    let expanded = expand_function_proof_source(source, &c, "countdown").unwrap();
    without_implicit_solve(|| verify_c_sources(&expanded, &c))
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: anonymous resource verification, expansion, and cold recheck"]
fn anonymous_resource_descent_completes_and_expands_without_a_source_walk() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/c_decreases_resource_avoids_recursive_loop.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.unwrap();
    let inputs = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c_sources(&source, &inputs).unwrap();
    let expanded = expand_function_proof_source(&source, &inputs, "walk").unwrap();
    without_implicit_solve(|| verify_c_sources(&expanded, &inputs))
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[cfg(feature = "fast-gate")]
test_batches! {
    file: "contract_closing_tests.rs",
    marker: "contract_closing_batch_",
    contract_closing_batch_00: [
        explicit_contract_closing_uses_ordinary_known_steps,
        implicit_contract_closing_expands_into_explicit_steps,
        per_clause_contract_closing_expands_after_its_source_proof,
        omitted_closing_steps_leave_their_obligations_open,
    ],
    contract_closing_batch_01: [
        written_solve_closes_only_one_selected_closing_goal,
        expansion_writes_each_closing_step_and_requires_them_when_cold,
        proposition_closers_name_the_pending_closing_goal,
        footprint_refusal_names_the_goal_and_the_solver_that_failed,
    ],
    contract_closing_batch_02: [
        grouped_source_only_claims_complete_and_expand_as_ordinary_proofs,
        separate_source_only_clauses_complete_their_own_cells,
        proving_one_source_only_clause_cannot_cover_a_false_sibling,
        concrete_and_avoided_loops_need_no_summary_measure,
    ],
    contract_closing_batch_03: [
        completed_descent_covers_a_concretely_avoided_recursive_loop,
        retained_context_does_not_discharge_an_unproved_recursive_descent,
        reassigned_numeric_parameter_descent_expands_into_ordinary_steps,
    ],
}
