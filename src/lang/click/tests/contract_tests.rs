use super::*;

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
fn flat_function_proof_stays_on_proof_through_claim_acceptance() {
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

    let ((((verified, certificate_checks), context_exports), replay_executions), flat_units) =
        proof::count_flat_proof_units(|| {
            proof::count_internal_proof_executions(|| {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        verify_c0_sources(click_source, &[("identity.c", c_source)])
                    })
                })
            })
        });
    verified.expect("the flat function proof should verify");
    assert_eq!(
        flat_units, 1,
        "the claim should finish from one retained Proof"
    );
    assert_eq!(
        replay_executions, 0,
        "flat verification must not enter execute_internal_proof"
    );
    assert_eq!(
        context_exports, 0,
        "the retained Proof must not export back into ProofReplayContext"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary flat verification must not check a source certificate"
    );
}

#[test]
fn grouped_flat_function_proof_stays_on_one_proof_through_claim_acceptance() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures first: result == result;
                ensures second: result == result;
            } by {
                execute();
                simp();
            }
        "#;

    let ((((verified, certificate_checks), context_exports), replay_executions), flat_units) =
        proof::count_flat_proof_units(|| {
            proof::count_internal_proof_executions(|| {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        verify_c0_sources(click_source, &[("identity.c", c_source)])
                    })
                })
            })
        });
    let verified = verified.expect("the grouped flat function proof should verify");
    assert_eq!(verified.len(), 2, "both grouped claims should be proved");
    assert_eq!(
        flat_units, 1,
        "the grouped claims should finish from one retained Proof"
    );
    assert_eq!(
        replay_executions, 0,
        "grouped flat verification must not enter execute_internal_proof"
    );
    assert_eq!(
        context_exports, 0,
        "the retained grouped Proof must not export into ProofReplayContext"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary grouped flat verification must not check a source certificate"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Grouped,
    )
    .expect("the retained grouped Proof should expand");
    assert!(!expanded.contains("execute();"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the grouped rewrite should verify normally");

    let corrupted = expanded.replacen("have result == result", "have result != result", 1);
    assert_ne!(
        corrupted, expanded,
        "grouped expansion should expose a checked have"
    );
    verify_c0_sources(&corrupted, &[("identity.c", c_source)])
        .expect_err("tampering with a grouped extracted operation must invalidate the proof");
}

#[test]
fn flat_function_expansion_rewrites_and_rejects_tampering() {
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

    let expanded = expand_c0_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Ensure(0),
    )
    .expect("the retained flat Proof should expand");
    assert!(!expanded.contains("execute();"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the rewritten source should verify normally");

    let corrupted = expanded.replacen("have result == x", "have result != x", 1);
    assert_ne!(
        corrupted, expanded,
        "expansion should expose its checked have"
    );
    verify_c0_sources(&corrupted, &[("identity.c", c_source)])
        .expect_err("tampering with an extracted operation must invalidate the source proof");
}

#[test]
fn post_execution_frame_using_relowers_a_preceding_have_fact() {
    let c_source = r#"
            int32 clear_first(int32* data) {
                data[0] = 0;
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "clear_first.c";

            int32 clear_first(int32 data[]) {
                consumes data[0..1];
                produces data[0..1];
                mutable data[0..1];
                ensures data[0] == 0;
            } by {
                execute();
                have data[0] == 0 by {
                    assumption();
                }
                frame() using {
                    data[0] == 0;
                }
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("clear_first.c", c_source)])
        .expect("frame premises should use facts established by preceding exit haves");
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
    assert!(error.message().contains("real-time limit"), "{error:?}");
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
fn smart_frame_reports_its_real_time_deadline() {
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

    assert!(error.message().contains("real-time limit"), "{error:?}");
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

    let offset = click_source.find("auto").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("write_i_read_j.c", c_source)],
        position.line,
        position.column,
    )
    .expect("unwritten read should expand through explicit transport");
    assert!(expanded.contains("transport("), "{expanded}");
    assert!(expanded.contains("separate("), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("write_i_read_j.c", c_source)])
        .expect("expanded unwritten-read transport should replay");
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

    let ((verified, events), planning_transitions) = collect_planning_statement_transitions(|| {
        crate::instrumentation::collect(|| {
            verify_c0_sources(click_source, &[("write_in_bounds.c", c_source)])
        })
    });
    let verified = verified.expect("contextual frame should verify");
    assert!(
        planning_transitions.is_empty(),
        "the complete effect script must search only on checked Proof descendants: \
         {planning_transitions:#?}"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name.starts_with("smart tactic compatibility replay")
        )),
        "the complete effect script must not enter compatibility replay: {events:#?}"
    );
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
    let statement_steps = expanded
        .iter()
        .filter_map(|tactic| match tactic {
            ProofTactic::StepUsing(premises) => Some(premises),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        statement_steps.len(),
        2,
        "the store and return should each occur exactly once in the retained certificate: {expanded:#?}"
    );
    assert!(
        statement_steps
            .iter()
            .all(|premises| !format!("{premises:?}").contains("unrelated")),
        "statement selection leaked an unrelated indexed fact: {statement_steps:#?}"
    );
    assert!(
        !format!("{expanded:?}").contains("Derive("),
        "contextual frame expansion retained a legacy derive certificate: {expanded:?}"
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
    ProofCertificate::from_proof_tactics(&expanded)
        .expect("contextual frame expansion should be a surface certificate");
}

#[test]
fn grouped_contextual_frame_retains_complete_effect_script_on_proof() {
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
                mutable p[0..n];
            } by {
                execute();
                frame();
            }
        "#;

    let (result, flat_units) = proof::count_flat_proof_units(|| {
        proof::count_internal_proof_executions(|| {
            proof::count_execution_context_exports(|| {
                proof::count_source_certificate_checks(|| {
                    collect_planning_statement_transitions(|| {
                        crate::instrumentation::collect(|| {
                            verify_c0_sources(click_source, &[("write_in_bounds.c", c_source)])
                        })
                    })
                })
            })
        })
    });
    let (result, replay_executions) = result;
    let (result, context_exports) = result;
    let (result, certificate_checks) = result;
    let ((verified, events), planning_transitions) = result;
    let verified = verified.expect("the grouped effect proof should verify");
    assert_eq!(
        flat_units, 1,
        "the grouped effect proof should retain one Proof"
    );
    assert_eq!(
        replay_executions, 0,
        "the grouped effect proof must not enter execute_internal_proof"
    );
    assert_eq!(
        context_exports, 0,
        "the grouped effect Proof must not export into ProofReplayContext"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary grouped effect verification must not check a source certificate"
    );
    assert!(
        planning_transitions.is_empty(),
        "the complete grouped effect script must search only on checked Proof descendants: \
         {planning_transitions:#?}"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name.starts_with("smart tactic compatibility replay")
        )),
        "the complete grouped effect script must not enter compatibility replay: {events:#?}"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the grouped effect proof should retain a simple certificate");
    assert_eq!(
        expanded
            .iter()
            .filter(|tactic| matches!(tactic, ProofTactic::StepUsing(_)))
            .count(),
        2,
        "the grouped store and return should each be retained exactly once: {expanded:#?}"
    );
    assert!(
        !format!("{expanded:?}").contains("unrelated"),
        "the grouped certificate selected an unrelated indexed fact: {expanded:#?}"
    );
    assert!(matches!(
        expanded.last(),
        Some(ProofTactic::FrameUsing { region: None, .. })
    ));
    ProofCertificate::from_proof_tactics(&expanded)
        .expect("the grouped effect expansion should be a simple certificate");

    let expanded_source = expand_c0_claim_source(
        click_source,
        &[("write_in_bounds.c", c_source)],
        "write_in_bounds",
        CProofClaim::Grouped,
    )
    .expect("the grouped effect proof should expand");
    verify_c0_sources(&expanded_source, &[("write_in_bounds.c", c_source)])
        .expect("the grouped retained certificate should independently verify");
}

#[test]
fn grouped_contextual_frame_combines_multiple_effect_certificates_on_proof() {
    let c_source = r#"
            int32 write_both(int32* p, int32* q, int32 n, int32* unrelated) {
                p[0] = 1;
                q[0] = 2;
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "write_both.c";

            int32 write_both(int32* p, int32* q, int32 n, int32* unrelated) {
                requires n >= 1;
                requires loadable(p[0..1]);
                requires loadable(q[0..1]);
                requires loadable(unrelated[0..1]);
                consumes p[0..1];
                consumes q[0..1];
                mutable p[0..1], q[0..1];
                mutable p[0..n], q[0..n];
            } by {
                execute();
                frame();
            }
        "#;

    let ((verified, events), planning_transitions) = collect_planning_statement_transitions(|| {
        crate::instrumentation::collect(|| {
            verify_c0_sources(click_source, &[("write_both.c", c_source)])
        })
    });
    let verified = verified.expect("the grouped multi-effect proof should verify");
    assert!(
        planning_transitions.is_empty(),
        "the grouped multi-effect script must search only on checked Proof descendants: \
         {planning_transitions:#?}"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name.starts_with("smart tactic compatibility replay")
        )),
        "the grouped multi-effect script must not enter compatibility replay: {events:#?}"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the grouped multi-effect proof should retain a simple certificate");
    assert_eq!(
        expanded
            .iter()
            .filter(|tactic| matches!(tactic, ProofTactic::StepUsing(_)))
            .count(),
        3,
        "both stores and the return should be retained exactly once: {expanded:#?}"
    );
    assert!(
        !format!("{expanded:?}").contains("unrelated"),
        "the grouped multi-effect certificate selected an unrelated fact: {expanded:#?}"
    );
    ProofCertificate::from_proof_tactics(&expanded)
        .expect("the grouped multi-effect expansion should be a simple certificate");

    let expanded_source = expand_c0_claim_source(
        click_source,
        &[("write_both.c", c_source)],
        "write_both",
        CProofClaim::Grouped,
    )
    .expect("the grouped multi-effect proof should expand");
    verify_c0_sources(&expanded_source, &[("write_both.c", c_source)])
        .expect("the grouped multi-effect certificate should independently verify");
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

    let ((((verified, certificate_checks), context_exports), replay_executions), flat_units) =
        proof::count_flat_proof_units(|| {
            proof::count_internal_proof_executions(|| {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        verify_c0_sources(click_source, &[("write_selected.c", c_source)])
                    })
                })
            })
        });
    let verified = verified.expect("branched contextual frame should verify");
    assert_eq!(flat_units, 1, "the effect claim should retain one Proof");
    assert_eq!(
        replay_executions, 0,
        "the effect proof entered legacy replay"
    );
    assert_eq!(context_exports, 0, "the effect Proof exported its state");
    assert_eq!(
        certificate_checks, 0,
        "ordinary effect verification replayed a certificate"
    );
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
    assert!(
        matches!(
            proof_if.then_tactics.last(),
            Some(ProofTactic::FrameUsing { region: None, .. })
        ),
        "then branch lost its terminal frame: {expanded:#?}"
    );
    assert!(
        matches!(
            proof_if.else_tactics.last(),
            Some(ProofTactic::FrameUsing { region: None, .. })
        ),
        "else branch lost its terminal frame: {expanded:#?}"
    );
    ProofCertificate::from_proof_tactics(&expanded)
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
        error.message().contains("unclosed goal: p[1] == old(p[1])"),
        "{}",
        error.message()
    );
}
