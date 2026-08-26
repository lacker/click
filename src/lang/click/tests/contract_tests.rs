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
fn individual_linear_open_proof_stays_on_proof_through_claim_acceptance() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            resource marker(x: int32) {
                fact x == x;
            }

            verifying "identity.c";

            int32 identity(int32 x) {
                consumes marker(x);
                ensures returns_x: result == x by {
                    open(marker(x)) {
                        execute();
                    }
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
    verified.expect("the individual open proof should verify");
    assert_eq!(flat_units, 1, "the open claim should finish from one Proof");
    assert_eq!(replay_executions, 0, "the open claim entered legacy replay");
    assert_eq!(context_exports, 0, "the open claim exported semantic state");
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification checked a certificate"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Ensure(0),
    )
    .expect("the individual open proof should expand");
    assert!(expanded.contains("open(marker(x))"), "{expanded}");
    assert!(!expanded.contains("execute();"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the rewritten individual open proof should verify normally");

    let checked_step = "                        step();\n";
    let corrupted = expanded.replacen(checked_step, "", 1);
    assert_ne!(
        corrupted, expanded,
        "expansion should expose the return step"
    );
    verify_c0_sources(&corrupted, &[("identity.c", c_source)])
        .expect_err("removing the scoped return step must invalidate the rewritten proof");
}

#[test]
fn explicit_call_partition_if_stays_on_one_proof_after_scoped_open() {
    let replace_source = r#"
            struct cell_owner {
                int32* data;
            };

            int32 replace_allocated_cell(struct cell_owner* owner) {
                int32* old_data;
                int32* new_data;

                old_data = owner->data;
                new_data = malloc(4);
                if (new_data == 0) {
                    return 0;
                }
                new_data[0] = 7;
                owner->data = new_data;
                free(old_data);
                return 1;
            }
        "#;
    let caller_source = r#"
            struct cell_owner {
                int32* data;
            };

            int32 replace_after_scoped_open(struct cell_owner* owner) {
                int32 replaced;

                replaced = replace_allocated_cell(owner);
                return replaced;
            }
        "#;
    let click_source = r#"
            resource allocated_cell(owner: struct cell_owner*) {
                owns owner->data;
                contains allocation(owner->data, 4);
                owns owner->data[0..1];
            }

            verifying "replace_allocated_cell.c";
            verifying "replace_after_scoped_open.c";

            int32 replace_allocated_cell(struct cell_owner* owner) {
                consumes allocated_cell(owner);
                mutable owner->data, owner->data[0..1];
                produces allocated_cell(owner);

                ensures result == 0 or result == 1;
                ensures result == 0 implies owner->data == old(owner->data);
            } by {
                unfold(allocated_cell(owner));
                execute();
                fold(allocated_cell(owner));
                frame();
                simp();
            }

            int32 replace_after_scoped_open(struct cell_owner* owner) {
                consumes allocated_cell(owner);
                mutable owner->data, owner->data[0..1];
                produces allocated_cell(owner);

                ensures result == 0 or result == 1;
            } by {
                open(allocated_cell(owner)) {
                }
                step() using {
                }
                step() using {
                }
                if at(statement(1).exit, owner->data) == old(owner->data) {
                    step();
                } else {
                    step();
                }
                frame();
                simp();
            }
        "#;
    let sources = &[
        ("replace_allocated_cell.c", replace_source),
        ("replace_after_scoped_open.c", caller_source),
    ];

    let (
        (
            ((((verified, certificate_checks), _context_exports), _replay_executions), flat_units),
            replay_labels,
        ),
        export_labels,
    ) = proof::collect_execution_context_export_labels(|| {
        proof::collect_internal_proof_execution_labels(|| {
            proof::count_flat_proof_units(|| {
                proof::count_internal_proof_executions(|| {
                    proof::count_execution_context_exports(|| {
                        proof::count_source_certificate_checks(|| {
                            verify_c0_sources(click_source, sources)
                        })
                    })
                })
            })
        })
    });
    verified.expect("the explicit call partition should remain on one retained Proof");
    assert_eq!(
        flat_units, 1,
        "only the caller's source proof should enter the direct Proof driver"
    );
    assert!(
        replay_labels
            .iter()
            .any(|label| label == "replace_allocated_cell.contract"),
        "the compatibility-backed callee should expose its real source path"
    );
    assert!(
        replay_labels
            .iter()
            .all(|label| label != "replace_after_scoped_open.contract"),
        "the caller entered legacy replay: {replay_labels:?}"
    );
    assert!(
        export_labels
            .iter()
            .all(|label| label != "replace_after_scoped_open.contract"),
        "the caller exported semantic state: {export_labels:?}"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification must not check a stitched certificate"
    );
}

pub(super) fn result_case_split_sources() -> (&'static str, &'static str, &'static str) {
    let replace_source = r#"
            struct cell_owner {
                int32* data;
            };

            int32 replace_allocated_cell(struct cell_owner* owner) {
                int32* old_data;
                int32* new_data;

                old_data = owner->data;
                new_data = malloc(4);
                if (new_data == 0) {
                    return 0;
                }
                new_data[0] = 7;
                owner->data = new_data;
                free(old_data);
                return 1;
            }
        "#;
    let caller_source = r#"
            struct cell_owner {
                int32* data;
            };

            int32 replace_then_branch(struct cell_owner* owner) {
                int32 replaced;

                replaced = replace_allocated_cell(owner);
                if (replaced == 0) {
                    return 0;
                } else {
                    return 1;
                }
            }
        "#;
    let click_source = r#"
            resource allocated_cell(owner: struct cell_owner*) {
                owns owner->data;
                contains allocation(owner->data, 4);
                owns owner->data[0..1];
            }

            verifying "replace_allocated_cell.c";
            verifying "replace_then_branch.c";

            int32 replace_allocated_cell(struct cell_owner* owner) {
                consumes allocated_cell(owner);
                mutable owner->data, owner->data[0..1];
                produces allocated_cell(owner);

                ensures result == 0 or result == 1;
                ensures result == 0 implies owner->data == old(owner->data);
                ensures owner->data == old(owner->data) implies result == 0;
                ensures result == 1 implies not owner->data == old(owner->data);
            } by {
                unfold(allocated_cell(owner));
                execute();
                fold(allocated_cell(owner));
                frame();
                simp();
            }

            int32 replace_then_branch(struct cell_owner* owner) {
                consumes allocated_cell(owner);
                mutable owner->data, owner->data[0..1];
                produces allocated_cell(owner);

                ensures result == 0 or result == 1;
            } by {
                open(allocated_cell(owner)) {
                }
                step() using {
                }
                step() using {
                }
                if c(replaced) == 0 {
                    step() using {
                        c(replaced) == 0 implies
                            at(statement(1).exit, owner->data) == old(owner->data);
                    }
                    step();
                } else {
                    step() using {
                        at(statement(1).exit, owner->data) == old(owner->data)
                            implies c(replaced) == 0;
                    }
                    step();
                }
                frame();
                simp();
            }
        "#;

    (replace_source, caller_source, click_source)
}

#[test]
fn result_case_split_collapses_call_successors_at_following_c_if() {
    let (replace_source, caller_source, click_source) = result_case_split_sources();
    let sources = &[
        ("replace_allocated_cell.c", replace_source),
        ("replace_then_branch.c", caller_source),
    ];

    verify_c0_sources(click_source, sources)
        .expect("the result split should collapse the two call successors at the next C `if`");
    let expanded = expand_c0_claim_source(
        click_source,
        sources,
        "replace_then_branch",
        CProofClaim::Grouped,
    )
    .expect("the collapsed result split should retain an expandable proof");
    verify_c0_sources(&expanded, sources)
        .expect("the collapsed result split expansion should replay independently");

    let insufficient = click_source
        .replace(
            "                    step() using {\n                        c(replaced) == 0 implies\n                            at(statement(1).exit, owner->data) == old(owner->data);\n                    }",
            "                    step() using {\n                    }",
        )
        .replace(
            "                    step() using {\n                        at(statement(1).exit, owner->data) == old(owner->data)\n                            implies c(replaced) == 0;\n                    }",
            "                    step() using {\n                    }",
        );
    let error = verify_c0_sources(&insufficient, sources)
        .expect_err("the adapter must decline when neither arm proves lane exclusion");
    assert!(
        error
            .message()
            .contains("does not name the preceding statement's certified partition"),
        "{error:?}"
    );
}

#[test]
fn proof_if_splits_one_frontier_after_execution_has_started() {
    let c_source = r#"
            int32 identity_after_prefix(int32 x) {
                int32 copied;

                copied = x;
                return copied;
            }
        "#;
    let click_source = r#"
            verifying "identity_after_prefix.c";

            int32 identity_after_prefix(int32 x) {
                immutable;
                ensures result == x;
            } by {
                step() using {
                }
                if x >= 0 {
                    step();
                    step();
                } else {
                    step();
                    step();
                }
                frame();
                simp();
            }
        "#;
    let sources = &[("identity_after_prefix.c", c_source)];

    let ((((verified, certificate_checks), context_exports), replay_executions), flat_units) =
        proof::count_flat_proof_units(|| {
            proof::count_internal_proof_executions(|| {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        verify_c0_sources(click_source, sources)
                    })
                })
            })
        });
    verified.expect("the mid-execution proof case split should remain on one retained Proof");
    assert_eq!(flat_units, 1, "the contract should retain one Proof");
    assert_eq!(
        replay_executions, 0,
        "the split must not enter legacy replay"
    );
    assert_eq!(
        context_exports, 0,
        "the split must not export semantic state"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification must not check a stitched certificate"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        sources,
        "identity_after_prefix",
        CProofClaim::Grouped,
    )
    .expect("the retained mid-execution case split should expand");
    assert!(expanded.contains("if x >= 0"), "{expanded}");
    verify_c0_sources(&expanded, sources)
        .expect("the expanded mid-execution case split should verify independently");
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
fn grouped_n_way_function_outcomes_stay_on_one_proof() {
    let c_source = r#"
            int32 classify(int32 x) {
                if (x < 0) {
                    return -1;
                }
                if (x == 0) {
                    return 0;
                }
                return 1;
            }
        "#;
    let click_source = r#"
            verifying "classify.c";

            int32 classify(int32 x) {
                ensures lower: result >= -1;
                ensures upper: result <= 1;
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
                        verify_c0_sources(click_source, &[("classify.c", c_source)])
                    })
                })
            })
        });
    let verified = verified.expect("the grouped N-way function proof should verify");
    assert_eq!(
        verified.len(),
        6,
        "both claims should be proved on each of the three outcomes"
    );
    assert_eq!(flat_units, 1, "all outcomes should stay on one Proof");
    assert_eq!(
        replay_executions, 0,
        "grouped N-way verification must not enter execute_internal_proof"
    );
    assert_eq!(
        context_exports, 0,
        "the grouped N-way Proof must not export into ProofReplayContext"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary grouped N-way verification must not check a source certificate"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &[("classify.c", c_source)],
        "classify",
        CProofClaim::Grouped,
    )
    .expect("the retained grouped N-way Proof should expand");
    assert!(!expanded.contains("execute();"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_c0_sources(&expanded, &[("classify.c", c_source)])
        .expect("the expanded grouped N-way proof should verify normally");
}

#[test]
fn grouped_n_way_outcomes_discard_exactly_infeasible_siblings_on_proof() {
    let c_source = r#"
            int32 pointer_is_null(int32* p) {
                return p == 0;
            }
        "#;
    let click_source = r#"
            verifying "pointer_is_null.c";

            int32 pointer_is_null(int32* p) {
                requires p == 0;
                ensures result == 1;
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
                        verify_c0_sources(click_source, &[("pointer_is_null.c", c_source)])
                    })
                })
            })
        });
    let verified = verified.expect("the feasible grouped outcome should verify");
    assert_eq!(verified.len(), 1);
    assert_eq!(flat_units, 1, "the selected outcome should stay on Proof");
    assert_eq!(replay_executions, 0);
    assert_eq!(context_exports, 0);
    assert_eq!(certificate_checks, 0);

    let expanded = expand_c0_claim_source(
        click_source,
        &[("pointer_is_null.c", c_source)],
        "pointer_is_null",
        CProofClaim::Grouped,
    )
    .expect("the feasible grouped outcome should expand");
    verify_c0_sources(&expanded, &[("pointer_is_null.c", c_source)])
        .expect("the rewritten feasible-outcome proof should verify normally");
}

#[test]
fn grouped_calls_keep_contract_transitions_on_proof() {
    let set_source = r#"
            void set_one(int32* data, int32 permit) {
                data[0] = 1;
            }
        "#;
    let caller_source = r#"
            int32 call_set_one(int32* data, int32 permit) {
                set_one(data, permit);
                return data[0];
            }
        "#;
    let click_source = r#"
            verifying "set_one.c";
            verifying "call_set_one.c";

            void set_one(int32 data[], int32 permit) {
                requires permit >= 0;
                owns data[0..1];
                mutable data[0..1];
                ensures data[0] == 1;
            } by {
                execute();
                frame();
                simp();
            }

            int32 call_set_one(int32 data[], int32 permit) {
                requires permit >= 1;
                owns data[0..1];
                mutable data[0..1];
                ensures exact: result == 1;
                ensures post_call: data[0] == 1;
            } by {
                execute();
                frame();
                simp();
            }
        "#;
    let sources = &[("set_one.c", set_source), ("call_set_one.c", caller_source)];

    let ((((verified, certificate_checks), context_exports), replay_executions), flat_units) =
        proof::count_flat_proof_units(|| {
            proof::count_internal_proof_executions(|| {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        verify_c0_sources(click_source, sources)
                    })
                })
            })
        });
    verified.expect("the grouped call and callee proofs should verify");
    assert_eq!(flat_units, 2, "both functions should retain one Proof");
    assert_eq!(
        replay_executions, 0,
        "the grouped caller must not enter execute_internal_proof"
    );
    assert_eq!(
        context_exports, 0,
        "the grouped caller must not export its checked call state"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary grouped call verification must not check a source certificate"
    );

    let expanded =
        expand_c0_claim_source(click_source, sources, "call_set_one", CProofClaim::Grouped)
            .expect("the retained grouped call Proof should expand");
    let caller_expansion = expanded
        .split("int32 call_set_one")
        .nth(1)
        .expect("the expanded source should retain the selected caller");
    assert!(!caller_expansion.contains("execute();"), "{expanded}");
    assert!(!caller_expansion.contains("frame();"), "{expanded}");
    assert!(!caller_expansion.contains("simp();"), "{expanded}");
    assert!(caller_expansion.contains("step();"), "{expanded}");
    verify_c0_sources(&expanded, sources)
        .expect("the rewritten grouped call proof should verify normally");

    // The call step runs in the caller's context; its prerequisite is the
    // caller's requirement, and removing that requirement invalidates it.
    let corrupted = expanded.replacen("requires permit >= 1;", "", 1);
    assert_ne!(
        corrupted, expanded,
        "the caller's requirement should be present"
    );
    verify_c0_sources(&corrupted, sources)
        .expect_err("removing the call prerequisite from the context must invalidate the proof");
}

#[test]
fn outcome_simp_spells_a_call_postcondition_across_two_snapshots() {
    // `touch` may write both fields and certifies `p->x == old(p->x)`: after
    // each call the caller's `p->x` is a fresh cell related to its previous
    // value only by that certified fact, and no single execution point
    // denotes both operands. Two calls make the caller's outcome a chain of
    // two such facts, so the outcome `simp` must cite them as premises,
    // spelled with one anchor per operand, and close through the checked
    // linear search, never the planner.
    let touch_source = r#"
            void touch(struct pair* p) {
                int32 kept;
                kept = p->x;
                p->y = 1;
                p->x = kept;
            }
        "#;
    let keep_source = r#"
            int32 keep_x(struct pair* p) {
                touch(p);
                touch(p);
                return p->x;
            }
        "#;
    let click_source = r#"
            verifying "touch.c";
            verifying "keep_x.c";

            void touch(struct pair* p) {
                requires p != 0;
                owns p->x;
                owns p->y;
                mutable p->x, p->y;
                ensures p->x == old(p->x);
                ensures p->y == 1;
            } by {
                execute();
                frame();
                simp();
            }

            int32 keep_x(struct pair* p) {
                requires p != 0;
                owns p->x;
                owns p->y;
                mutable p->x, p->y;
                ensures result == old(p->x);
            } by {
                execute();
                frame();
                simp();
            }
        "#;
    let struct_source = "struct pair { int32 x; int32 y; };\n";
    let touch_source = format!("{struct_source}{touch_source}");
    let keep_source = format!("{struct_source}{keep_source}");
    let sources = &[
        ("touch.c", touch_source.as_str()),
        ("keep_x.c", keep_source.as_str()),
    ];

    let ((verified, _events), planning_transitions) =
        collect_planning_statement_transitions(|| {
            crate::instrumentation::collect(|| verify_c0_sources(click_source, sources))
        });
    verified.expect("the caller should verify through the checked linear search");
    assert!(
        planning_transitions.is_empty(),
        "the caller's outcome must close without planner construction: {planning_transitions:#?}"
    );

    let expanded = expand_c0_claim_source(click_source, sources, "keep_x", CProofClaim::Grouped)
        .expect("the retained caller Proof should expand");
    let caller_expansion = expanded
        .split("int32 keep_x")
        .nth(1)
        .expect("the expanded source should retain the caller");
    // Rewriting with the later fact leaves the earlier one as the exact
    // goal, which closes by assumption.
    let premise = "rewrite(at(statement(2).entry, p->x) == at(statement(1).entry, p->x));";
    assert!(
        caller_expansion.contains(premise),
        "the outcome closer should cite the preserved field with one anchor per snapshot: {expanded}"
    );
    verify_c0_sources(&expanded, sources)
        .expect("the rewritten caller proof should verify normally");
}

#[test]
fn grouped_opaque_calls_keep_declared_composite_resources_on_proof() {
    let borrow_source = r#"
            int32 borrow_token(int32 key) {
                return key;
            }
        "#;
    let caller_source = r#"
            int32 borrow_token_twice(int32 key) {
                int32 value;
                value = borrow_token(key);
                value = borrow_token(key);
                return value;
            }
        "#;
    let click_source = r#"
            abstract resource token(key: int32);

            resource token_bundle(key: int32) {
                contains token(key);
            }

            verifying "borrow_token.c";
            verifying "borrow_token_twice.c";

            int32 borrow_token(int32 key) {
                consumes token_bundle(key);
                produces token_bundle(key);
                ensures result == key;
            } by {
                execute();
                simp();
            }

            int32 borrow_token_twice(int32 key) {
                consumes token_bundle(key);
                produces token_bundle(key);
                ensures result == key;
            } by {
                execute();
                simp();
            }
        "#;
    let sources = &[
        ("borrow_token.c", borrow_source),
        ("borrow_token_twice.c", caller_source),
    ];

    let ((((verified, certificate_checks), context_exports), replay_executions), flat_units) =
        proof::count_flat_proof_units(|| {
            proof::count_internal_proof_executions(|| {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        verify_c0_sources(click_source, sources)
                    })
                })
            })
        });
    verified.expect("declared composite resources should cross both checked calls");
    assert_eq!(flat_units, 2, "both functions should retain one Proof");
    assert_eq!(
        replay_executions, 0,
        "declared-resource calls must not replay"
    );
    assert_eq!(
        context_exports, 0,
        "declared-resource calls must not export replay state"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification must not check a certificate"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        sources,
        "borrow_token_twice",
        CProofClaim::Grouped,
    )
    .expect("the retained declared-resource call Proof should expand");
    let caller_expansion = expanded
        .split("int32 borrow_token_twice")
        .nth(1)
        .expect("the expanded source should retain the selected caller");
    assert!(!caller_expansion.contains("execute();"), "{expanded}");
    assert!(!caller_expansion.contains("simp();"), "{expanded}");
    assert_eq!(
        caller_expansion.matches("step();").count(),
        4,
        "each caller statement should retain one checked step: {expanded}"
    );
    verify_c0_sources(&expanded, sources)
        .expect("the rewritten declared-resource call proof should verify normally");

    let checked_step = "                step();\n";
    let corrupted = expanded.replacen(checked_step, "", 1);
    assert_ne!(
        corrupted, expanded,
        "expansion should expose checked call steps"
    );
    verify_c0_sources(&corrupted, sources)
        .expect_err("removing an extracted resource-bearing step must invalidate the proof");
}

#[test]
fn grouped_mutable_composite_calls_keep_open_scopes_on_proof() {
    let set_source = r#"
            int32 set_seven(int32* cell) {
                cell[0] = 7;
                return cell[0];
            }
        "#;
    let caller_source = r#"
            int32 set_wrapped_seven(int32* cell) {
                int32 value;
                value = set_seven(cell);
                return value;
            }
        "#;
    let click_source = r#"
            resource owned_cell(cell: int32*) {
                owns cell[0..1];
            }

            resource wrapped_cell(cell: int32*) {
                contains owned_cell(cell);
            }

            verifying "set_seven.c";
            verifying "set_wrapped_seven.c";

            int32 set_seven(int32* cell) {
                consumes owned_cell(cell);
                mutable cell[0..1];
                produces owned_cell(cell);
                ensures result == 7;
            } by {
                open(owned_cell(cell)) {
                    execute();
                    frame();
                }
                simp();
            }

            int32 set_wrapped_seven(int32* cell) {
                consumes wrapped_cell(cell);
                mutable cell[0..1];
                produces wrapped_cell(cell);
                ensures result == 7;
            } by {
                open(wrapped_cell(cell)) {
                    execute();
                    frame();
                }
                simp();
            }
        "#;
    let sources = &[
        ("set_seven.c", set_source),
        ("set_wrapped_seven.c", caller_source),
    ];

    let ((((verified, certificate_checks), context_exports), replay_executions), flat_units) =
        proof::count_flat_proof_units(|| {
            proof::count_internal_proof_executions(|| {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        verify_c0_sources(click_source, sources)
                    })
                })
            })
        });
    verified.expect("mutable composite resources should cross the scoped opaque call");
    assert_eq!(flat_units, 2, "both open-scope proofs should stay on Proof");
    assert_eq!(replay_executions, 0, "open scopes must not replay");
    assert_eq!(
        context_exports, 0,
        "open scopes must not export replay state"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification must not check a certificate"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        sources,
        "set_wrapped_seven",
        CProofClaim::Grouped,
    )
    .expect("the retained mutable composite call scope should expand");
    let caller_expansion = expanded
        .split("int32 set_wrapped_seven")
        .nth(1)
        .expect("the expanded source should retain the selected caller");
    assert!(
        caller_expansion.contains("open(wrapped_cell(cell))"),
        "{expanded}"
    );
    assert!(!caller_expansion.contains("execute();"), "{expanded}");
    assert!(!caller_expansion.contains("frame();"), "{expanded}");
    assert!(!caller_expansion.contains("simp();"), "{expanded}");
    verify_c0_sources(&expanded, sources)
        .expect("the rewritten scoped composite-call proof should verify normally");

    let checked_step = "                    step();\n";
    let corrupted = expanded.replacen(checked_step, "", 1);
    assert_ne!(
        corrupted, expanded,
        "expansion should expose a scoped call step"
    );
    verify_c0_sources(&corrupted, sources)
        .expect_err("removing the scoped call step must invalidate the rewritten proof");
}

#[test]
fn grouped_mutable_composite_calls_continue_on_proof_after_preparatory_scope() {
    let set_source = r#"
            int32 set_seven(int32* cell, int32 choose) {
                if (choose == 0) {
                    return 0;
                }
                cell[0] = 7;
                return 1;
            }
        "#;
    let caller_source = r#"
            int32 prepare_then_set_seven(int32* cell, int32 choose) {
                int32 value;
                value = set_seven(cell, choose);
                return value;
            }
        "#;
    let click_source = r#"
            resource owned_cell(cell: int32*) {
                owns cell[0..1];
            }

            resource wrapped_cell(cell: int32*) {
                contains owned_cell(cell);
            }

            verifying "set_seven.c";
            verifying "prepare_then_set_seven.c";

            int32 set_seven(int32* cell, int32 choose) {
                consumes owned_cell(cell);
                mutable cell[0..1];
                produces owned_cell(cell);
                ensures result == 0 or result == 1;
            } by {
                open(owned_cell(cell)) {
                    execute();
                    frame();
                }
                simp();
            }

            int32 prepare_then_set_seven(int32* cell, int32 choose) {
                consumes wrapped_cell(cell);
                mutable cell[0..1];
                produces wrapped_cell(cell);
                ensures result == 0 or result == 1;
            } by {
                open(wrapped_cell(cell)) {
                }
                execute();
                frame();
                simp();
            }
        "#;
    let sources = &[
        ("set_seven.c", set_source),
        ("prepare_then_set_seven.c", caller_source),
    ];

    let ((((verified, certificate_checks), context_exports), replay_executions), flat_units) =
        proof::count_flat_proof_units(|| {
            proof::count_internal_proof_executions(|| {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        verify_c0_sources(click_source, sources)
                    })
                })
            })
        });
    verified.expect("the closed preparatory scope should continue through the checked call");
    assert_eq!(flat_units, 2, "both functions should retain one Proof");
    assert_eq!(
        replay_executions, 0,
        "the preparatory scope continuation must not replay"
    );
    assert_eq!(
        context_exports, 0,
        "the closed preparatory scope must not export replay state"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification must not check a certificate"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        sources,
        "prepare_then_set_seven",
        CProofClaim::Grouped,
    )
    .expect("the retained preparatory scope Proof should expand");
    let caller_expansion = expanded
        .split("int32 prepare_then_set_seven")
        .nth(1)
        .expect("the expanded source should retain the selected caller");
    assert!(!caller_expansion.contains("execute();"), "{expanded}");
    assert!(!caller_expansion.contains("frame();"), "{expanded}");
    assert!(!caller_expansion.contains("simp();"), "{expanded}");
    assert!(caller_expansion.contains("open(wrapped_cell(cell))"));
    verify_c0_sources(&expanded, sources)
        .expect("the rewritten preparatory-scope proof should verify normally");
}

#[test]
fn grouped_sequential_top_level_scopes_stay_on_one_proof() {
    let c_source = r#"
            int32 add_twice(int32 x) {
                int32 first;
                first = x + 1;
                return first + 1;
            }
        "#;
    let click_source = r#"
            resource first_marker(x: int32) {
                fact x == x;
            }

            resource second_marker(x: int32) {
                fact x == x;
            }

            verifying "add_twice.c";

            int32 add_twice(int32 x) {
                requires x >= 0;
                requires x <= 2147483645;
                owns first_marker(x);
                owns second_marker(x);
                immutable;
                ensures result == (x + 1) + 1;
            } by {
                open(first_marker(x)) {
                    step();
                }
                open(second_marker(x)) {
                    execute();
                }
                frame();
                simp();
            }
        "#;
    let sources = &[("add_twice.c", c_source)];

    let ((((verified, certificate_checks), context_exports), replay_executions), flat_units) =
        proof::count_flat_proof_units(|| {
            proof::count_internal_proof_executions(|| {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        verify_c0_sources(click_source, sources)
                    })
                })
            })
        });
    verified.expect("both sequential scopes should advance one checked Proof");
    assert_eq!(flat_units, 1, "the function should retain one Proof");
    assert_eq!(replay_executions, 0, "sequential scopes must not replay");
    assert_eq!(
        context_exports, 0,
        "sequential scopes must not export semantic state"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification must not check a certificate"
    );

    let expanded = expand_c0_claim_source(click_source, sources, "add_twice", CProofClaim::Grouped)
        .expect("the retained sequential scopes should expand");
    let caller_expansion = expanded
        .split("int32 add_twice")
        .nth(1)
        .expect("the expanded source should retain the selected function");
    assert_eq!(
        caller_expansion.matches("open(").count(),
        2,
        "both top-level scopes should be serialized: {expanded}"
    );
    assert!(!caller_expansion.contains("execute();"), "{expanded}");
    assert!(!caller_expansion.contains("frame();"), "{expanded}");
    assert!(!caller_expansion.contains("simp();"), "{expanded}");
    verify_c0_sources(&expanded, sources)
        .expect("the rewritten sequential-scope proof should verify normally");

    let checked_step = "                    step();\n";
    let corrupted = expanded.replacen(checked_step, "", 1);
    assert_ne!(
        corrupted, expanded,
        "expansion should expose both checked statements"
    );
    verify_c0_sources(&corrupted, sources)
        .expect_err("removing one scoped statement must invalidate the rewritten proof");
}

#[test]
fn grouped_predicate_contracts_stay_on_one_proof() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            predicate nonnegative(x: int32) {
                x >= 0
            }

            predicate same(x: int32, y: int32) {
                x == y
            }

            int32 identity(int32 x) {
                requires nonnegative(x);
                ensures preserved: nonnegative(result);
                ensures exact: same(result, x);
            } by {
                execute();
                simp();
            }
        "#;
    let sources = &[("identity.c", c_source)];

    let ((((verified, certificate_checks), context_exports), replay_executions), flat_units) =
        proof::count_flat_proof_units(|| {
            proof::count_internal_proof_executions(|| {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        verify_c0_sources(click_source, sources)
                    })
                })
            })
        });
    let verified = verified.expect("the grouped predicate contract should verify");
    assert_eq!(verified.len(), 2, "both predicate claims should be proved");
    assert_eq!(
        flat_units, 1,
        "the predicate claims should stay on one Proof"
    );
    assert_eq!(
        replay_executions, 0,
        "predicate verification must not replay"
    );
    assert_eq!(
        context_exports, 0,
        "the predicate Proof must not export replay state"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification must not check a certificate"
    );

    let expanded = expand_c0_claim_source(click_source, sources, "identity", CProofClaim::Grouped)
        .expect("the retained predicate Proof should expand");
    assert!(
        expanded.contains("have nonnegative(result) by {"),
        "{expanded}"
    );
    assert!(expanded.contains("unfold(same);"), "{expanded}");
    assert!(!expanded.contains("execute();"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_c0_sources(&expanded, sources)
        .expect("the rewritten predicate proof should verify normally");

    let corrupted = expanded.replacen("unfold(same);", "unfold(nonnegative);", 1);
    assert_ne!(
        corrupted, expanded,
        "expansion should expose the predicate unfold"
    );
    verify_c0_sources(&corrupted, sources)
        .expect_err("tampering with the extracted predicate operation must fail");
}

#[test]
fn grouped_leading_resource_relations_stay_on_one_proof() {
    let c_source = r#"
            int32 inspect_pair(int32 left[], int32 right[]) {
                return 0;
            }
        "#;
    let click_source = r#"
            resource pair(left: int32[], right: int32[]) {
                owns left[0..1];
                owns right[0..1];
            }

            verifying "inspect_pair.c";

            int32 inspect_pair(int32 left[], int32 right[]) {
                requires contains(pair(left, right), memory(left[0..1]));
                requires separate(memory(left[0..1]), memory(right[0..1]));
                ensures result == 0;
            } by {
                have contains(pair(left, right), memory(left[0..1])) by {
                    assumption();
                }
                have separate(memory(left[0..1]), memory(right[0..1])) by {
                    assumption();
                }
                execute();
                simp();
            }
        "#;
    let sources = &[("inspect_pair.c", c_source)];

    let (
        (
            (((verified, explicit_fallbacks), certificate_checks), context_exports),
            replay_executions,
        ),
        flat_units,
    ) = proof::count_flat_proof_units(|| {
        proof::count_internal_proof_executions(|| {
            proof::count_execution_context_exports(|| {
                proof::count_source_certificate_checks(|| {
                    proof::count_explicit_linear_fallbacks(|| {
                        verify_c0_sources(click_source, sources)
                    })
                })
            })
        })
    });
    verified.expect("leading resource relations should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");
    assert_eq!(
        replay_executions, 0,
        "resource-relation haves must not replay"
    );
    assert_eq!(
        context_exports, 0,
        "resource-relation haves must not export semantic state"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary resource-relation verification must not check a certificate"
    );
    assert_eq!(
        explicit_fallbacks, 0,
        "resource-relation assumptions must apply directly to Proof"
    );

    let expanded =
        expand_c0_claim_source(click_source, sources, "inspect_pair", CProofClaim::Grouped)
            .expect("the retained resource-relation scopes should expand");
    assert!(
        expanded.contains("have contains(pair(left, right)"),
        "{expanded}"
    );
    assert!(
        expanded.contains("have separate(memory(left[0..1])"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, sources)
        .expect("the rewritten resource-relation proof should verify normally");

    for (relation, corrupted) in [
        (
            "containment",
            expanded.replacen(
                "have contains(pair(left, right), memory(left[0..1]))",
                "have contains(pair(left, right), memory(right[0..1]))",
                1,
            ),
        ),
        (
            "separation",
            expanded.replacen(
                "have separate(memory(left[0..1]), memory(right[0..1]))",
                "have separate(memory(left[0..1]), memory(left[0..1]))",
                1,
            ),
        ),
    ] {
        assert_ne!(corrupted, expanded, "expansion should expose {relation}");
        let ((corrupted_result, corrupted_fallbacks), corrupted_replays) =
            proof::count_internal_proof_executions(|| {
                proof::count_explicit_linear_fallbacks(|| verify_c0_sources(&corrupted, sources))
            });
        corrupted_result.expect_err(&format!(
            "tampering with {relation} must invalidate the proof"
        ));
        assert_eq!(
            corrupted_fallbacks, 0,
            "invalid migrated {relation} must not become a compatibility miss"
        );
        assert_eq!(
            corrupted_replays, 0,
            "invalid migrated {relation} must not enter replay"
        );
    }
}

#[test]
fn grouped_unfolded_resource_relations_stay_on_one_proof() {
    let c_source = r#"
            int32 inspect_pair(int32 left[], int32 right[]) {
                return 0;
            }
        "#;
    let click_source = r#"
            resource pair(left: int32[], right: int32[]) {
                owns left[0..1];
                owns right[0..1];
            }

            verifying "inspect_pair.c";

            int32 inspect_pair(int32 left[], int32 right[]) {
                owns pair(left, right);
                immutable;
                ensures result == 0;
            } by {
                observe(pair(left, right));
                unfold(pair(left, right));
                have contains(pair(left, right), memory(left[0..1])) by {
                    assumption();
                }
                have separate(memory(left[0..1]), memory(right[0..1])) by {
                    assumption();
                }
                fold(pair(left, right));
                execute();
                frame();
                simp();
            }
        "#;
    let sources = &[("inspect_pair.c", c_source)];

    let (
        (
            (((verified, explicit_fallbacks), certificate_checks), context_exports),
            replay_executions,
        ),
        flat_units,
    ) = proof::count_flat_proof_units(|| {
        proof::count_internal_proof_executions(|| {
            proof::count_execution_context_exports(|| {
                proof::count_source_certificate_checks(|| {
                    proof::count_explicit_linear_fallbacks(|| {
                        verify_c0_sources(click_source, sources)
                    })
                })
            })
        })
    });
    verified.expect("relations projected by an explicit unfold should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");
    assert_eq!(
        replay_executions, 0,
        "explicit resource operations and derived relations must not replay"
    );
    assert_eq!(
        context_exports, 0,
        "the unfolded resource proof must not export semantic state"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary unfolded-resource verification must not check a certificate"
    );
    assert_eq!(
        explicit_fallbacks, 0,
        "derived resource relations must apply directly to Proof"
    );

    let expanded =
        expand_c0_claim_source(click_source, sources, "inspect_pair", CProofClaim::Grouped)
            .expect("the retained unfolded-resource Proof should expand");
    assert!(
        expanded.contains("observe(pair(left, right));"),
        "{expanded}"
    );
    assert!(
        expanded.contains("unfold(pair(left, right));"),
        "{expanded}"
    );
    assert!(expanded.contains("fold(pair(left, right));"), "{expanded}");
    assert!(
        expanded.contains("have contains(pair(left, right)"),
        "{expanded}"
    );
    assert!(
        expanded.contains("have separate(memory(left[0..1])"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, sources)
        .expect("the rewritten unfolded-resource proof should verify normally");

    let corrupted = expanded.replacen(
        "have separate(memory(left[0..1]), memory(right[0..1]))",
        "have separate(memory(left[0..1]), memory(left[0..1]))",
        1,
    );
    assert_ne!(
        corrupted, expanded,
        "expansion should expose the derived separation"
    );
    let ((corrupted_result, corrupted_fallbacks), corrupted_replays) =
        proof::count_internal_proof_executions(|| {
            proof::count_explicit_linear_fallbacks(|| verify_c0_sources(&corrupted, sources))
        });
    corrupted_result.expect_err("tampering with the derived separation must fail");
    assert_eq!(
        corrupted_fallbacks, 0,
        "invalid migrated separation must not become a compatibility miss"
    );
    assert_eq!(
        corrupted_replays, 0,
        "invalid migrated separation must not enter replay"
    );
}

#[test]
fn grouped_mutable_outcome_resources_stay_on_one_proof() {
    let c_source = r#"
            int32 set_seven(int32* cell) {
                cell[0] = 7;
                return cell[0];
            }
        "#;
    let click_source = r#"
            resource seven_cell(cell: int32*) {
                owns cell[0..1];
                fact cell[0] == 7;
            }

            verifying "set_seven.c";

            int32 set_seven(int32* cell) {
                owns seven_cell(cell);
                mutable cell[0..1];
                ensures result == 7;
            } by {
                unfold(seven_cell(cell));
                execute();
                have cell[0] == 7 by {
                    simp();
                }
                fold(seven_cell(cell));
                frame() using {
                    cell[0] == 7;
                }
                simp();
            }
        "#;
    let sources = &[("set_seven.c", c_source)];

    let (
        (
            (((verified, explicit_fallbacks), certificate_checks), context_exports),
            replay_executions,
        ),
        flat_units,
    ) = proof::count_flat_proof_units(|| {
        proof::count_internal_proof_executions(|| {
            proof::count_execution_context_exports(|| {
                proof::count_source_certificate_checks(|| {
                    proof::count_explicit_linear_fallbacks(|| {
                        verify_c0_sources(click_source, sources)
                    })
                })
            })
        })
    });
    verified.expect("mutable outcome resource operations should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");
    assert_eq!(
        replay_executions, 0,
        "mutable outcome resource operations must not replay"
    );
    assert_eq!(
        context_exports, 0,
        "the mutable outcome Proof must not export semantic state"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary mutable outcome verification must not check a certificate"
    );
    assert_eq!(
        explicit_fallbacks, 0,
        "mutable outcome resource operations must apply directly to Proof"
    );

    let expanded = expand_c0_claim_source(click_source, sources, "set_seven", CProofClaim::Grouped)
        .expect("the retained mutable outcome Proof should expand");
    assert!(expanded.contains("unfold(seven_cell(cell));"), "{expanded}");
    assert!(expanded.contains("have cell[0] == 7 by {"), "{expanded}");
    assert!(expanded.contains("fold(seven_cell(cell));"), "{expanded}");
    verify_c0_sources(&expanded, sources)
        .expect("the rewritten mutable outcome proof should verify normally");

    let frame_fact = "cell[0] == 7;";
    let frame_fact_offset = expanded
        .rfind(frame_fact)
        .expect("expanded frame should retain its checked premise");
    let mut corrupted = expanded.clone();
    corrupted.replace_range(
        frame_fact_offset..frame_fact_offset + frame_fact.len(),
        "cell[0] == 8;",
    );
    assert_ne!(
        corrupted, expanded,
        "expansion should expose the post-execution frame premise"
    );
    let ((corrupted_result, corrupted_fallbacks), corrupted_replays) =
        proof::count_internal_proof_executions(|| {
            proof::count_explicit_linear_fallbacks(|| verify_c0_sources(&corrupted, sources))
        });
    corrupted_result.expect_err("tampering with the post-execution frame premise must fail");
    assert_eq!(
        corrupted_fallbacks, 0,
        "invalid migrated outcome work must not become a compatibility miss"
    );
    assert_eq!(
        corrupted_replays, 0,
        "invalid migrated outcome work must not enter replay"
    );
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
    // The steps run in the whole context, so the separation keeps the read
    // cell's name across the write and no explicit transport is needed.
    assert!(!expanded.contains("transport("), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("write_i_read_j.c", c_source)])
        .expect("expanded unwritten read should replay");
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
            ProofTactic::StepUsing(premises) => Some(premises.as_slice()),
            ProofTactic::Step => Some(&[][..]),
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
            .filter(|tactic| matches!(tactic, ProofTactic::Step | ProofTactic::StepUsing(_)))
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
            .filter(|tactic| matches!(tactic, ProofTactic::Step | ProofTactic::StepUsing(_)))
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
