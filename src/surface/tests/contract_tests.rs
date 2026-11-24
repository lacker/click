use super::*;

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_00")]
fn inline_array_element_addresses_are_logical_without_granting_access() {
    let source = r#"
        struct packet { int32 values[4]; uint8 bytes[4]; };
        void logical(struct packet* p) {}
        uint8* byte_at(struct packet* p, uint32 i) { return &p->bytes[i]; }
        int32 read(struct packet* p) { return p->values[0]; }
    "#;
    let inputs = [("addresses.c", source)];
    let proof = r#"verifying "addresses.c";
        void logical(struct packet* p) {
            ensures &p->values[0] == p->values;
        } by { step_until(function.exit); close(); }
        uint8* byte_at(struct packet* p, uint32 i) {
            views p->bytes[0..4];
            requires i < 4u32;
            ensures result == &p->bytes[i];
            ensures result == &p->bytes[0] + i;
        } by { step_until(function.exit); close(); }
    "#;
    let verified_for_expansion = verify_c_sources(proof, &inputs).unwrap();
    for (_, expanded) in
        expand_checked_grouped_claims(proof, &verified_for_expansion, ["logical", "byte_at"])
    {
        verify_c_sources(&expanded, &inputs).unwrap();
    }
    assert!(
        verify_c_sources(
            &proof.replace("&p->values[0] ==", "&p->values[1] =="),
            &inputs
        )
        .is_err()
    );
    assert!(
        verify_c_sources(
            &proof.replace("result == &p->bytes[i]", "result == &p->bytes[0]"),
            &inputs
        )
        .is_err()
    );
    for expression in ["defined(&p->values[5])", "defined(old(&p->values[5]))"] {
        let false_definedness = proof.replace("&p->values[0] == p->values", expression);
        assert!(
            verify_c_sources(&false_definedness, &inputs).is_err(),
            "{expression}"
        );
    }
    let missing_view = r#"verifying "addresses.c";
        int32 read(struct packet* p) {
            ensures &p->values[0] == p->values;
        } by { step_until(function.exit); close(); }
    "#;
    assert!(verify_c_sources(missing_view, &inputs).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_00")]
fn historical_wide_view_bound_reads_the_marked_counter() {
    let c = "unsigned long f(const unsigned char *p, unsigned n) { n = n - 1; return 0; }";
    for span in [16, 32] {
        let proof = format!(
            r#"
            verifying "retained_state.c";
            uint64 f(const uint8* p, uint32 n) {{
                requires n == 2u32;
                views p[0u64..{span}u64];
                ensures result == 0u64;
            }} by {{
                mark before;
                step();
                have to_integer(at(before, 16u64 * n as uint64)) == to_integer(32u64) by close();
                have at(before, viewable(p[0u64..16u64 * n as uint64])) by close();
                step_until(function.exit); close();
            }}
        "#
        );
        let result = verify_c_sources(&proof, &[("retained_state.c", c)]);
        if span == 16 {
            assert!(result.is_err(), "the saved counter needs 32 bytes, not 16");
        } else {
            result.unwrap();
            let expanded = expand_c_claim_source(
                &proof,
                &[("retained_state.c", c)],
                "f",
                ContractProofClaim::Ensure(0),
            )
            .unwrap();
            verify_c_sources(&expanded, &[("retained_state.c", c)]).unwrap();
        }
    }
}

#[test]
// Read-only C locals have actual storage and can initialize from a checked helper result.
fn readonly_scalar_initialization_preserves_address_and_expands() {
    let source = "int32 seven() { return 7; } int32 probe() { const int32 x = seven(); const int32* p = &x; return *p; }";
    let proof = r#"verifying "readonly.c";
        int32 seven() { ensures result == 7; }
        int32 probe() { ensures result == 7; }"#;
    verify_c_sources(proof, &[("readonly.c", source)]).unwrap();
    let expanded = expand_c_claim_source(
        proof,
        &[("readonly.c", source)],
        "probe",
        ContractProofClaim::Ensure(0),
    )
    .unwrap();
    verify_c_sources(&expanded, &[("readonly.c", source)]).unwrap();
}

#[test]
// A historical pointer value and the memory state of a load are independent.
fn typed_load_through_entry_pointer_reads_current_memory() {
    let source = "void probe(int32* p, int32* q) { *p = 7; p = q; }";
    let proof = r#"verifying "retained_state.c"; void probe(int32* p, int32* q) {
        owns p[0..1]; ensures load<int32>(old(p)) == 7;
    }"#;
    verify_c_sources(proof, &[("retained_state.c", source)]).unwrap();
    let expanded = expand_c_claim_source(
        proof,
        &[("retained_state.c", source)],
        "probe",
        ContractProofClaim::Ensure(0),
    )
    .unwrap();
    verify_c_sources(&expanded, &[("retained_state.c", source)]).unwrap();
    assert!(
        verify_c_sources(
            &proof.replace("load<int32>(old(p))", "old(load<int32>(p))"),
            &[("retained_state.c", source)]
        )
        .is_err()
    );
}

#[test]
// Pointer-valued historical loads must also keep their operand and print parseable certificates.
fn typed_pointer_load_through_entry_pointer_expands() {
    let source = "void probe(int32** p, int32* q, int32** r) { *p = q; p = r; }";
    let proof = r#"verifying "retained_state.c"; void probe(int32** p, int32* q, int32** r) {
        owns p[0..1]; ensures load<int32*>(old(p)) == q;
    }"#;
    verify_c_sources(proof, &[("retained_state.c", source)]).unwrap();
    let expanded = expand_c_claim_source(
        proof,
        &[("retained_state.c", source)],
        "probe",
        ContractProofClaim::Ensure(0),
    )
    .unwrap();
    verify_c_sources(&expanded, &[("retained_state.c", source)]).unwrap();
}

#[test]
// Byte views must retain allocation identity and scale subsequent offsets in bytes.
fn native_contract_byte_casts_preserve_pointer_identity_and_offsets() {
    let source = "uint32* probe(uint32* p) { return p + 1; }";
    let proof = r#"verifying "bytes.c";
        uint32* probe(uint32* p) {
            views p[0..1];
            ensures result as (uint8 *) == old((p + 1) as (uint8 *));
            ensures result as (uint8 *) == p as (uint8 *) + 4;
        }"#;
    verify_c_sources(proof, &[("bytes.c", source)]).unwrap();
    let expanded = expand_c_claim_source(
        proof,
        &[("bytes.c", source)],
        "probe",
        ContractProofClaim::Ensure(1),
    )
    .unwrap();
    verify_c_sources(&expanded, &[("bytes.c", source)]).unwrap();
}

#[test]
// Reject narrow scalar origins, pointer-slot byte views, and incompatible comparisons locally.
fn native_contract_byte_casts_check_their_type_boundary() {
    for (parameter, expression, diagnostic) in [
        (
            "uint32 p",
            "p as (uint8 *) == p as (uint8 *)",
            "scalar object pointer",
        ),
        (
            "uint32** p",
            "p as (uint8 *) == p as (uint8 *)",
            "scalar object pointer",
        ),
        (
            "uint32* p",
            "old(p) as (uint8 *) == p as (uint8 *)",
            "around the whole cast",
        ),
        (
            "uint32* p, uint8* q",
            "p == q",
            "incompatible pointer comparison",
        ),
    ] {
        let proof =
            format!("verifying \"bytes.c\"; int32 probe({parameter}) {{ ensures {expression}; }}");
        let source = format!("int32 probe({parameter}) {{ return 0; }}");
        let error = verify_c_sources(&proof, &[("bytes.c", &source)]).unwrap_err();
        assert!(error.message().contains(diagnostic), "{}", error.message());
    }
}

#[test]
// Retagging a pointer does not grant reads of bytes outside its initialized view.
fn native_contract_byte_casts_do_not_grant_memory_access() {
    let source = "uint8 probe(uint8* p) { return *p; }";
    let proof = r#"verifying "bytes.c"; uint8 probe(uint8* p) {
        views p[0..1]; ensures result == *(p as (uint8 *));
    }"#;
    verify_c_sources(proof, &[("bytes.c", source)]).unwrap();
    assert!(
        verify_c_sources(&proof.replace("views p[0..1];", ""), &[("bytes.c", source)]).is_err()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_00")]
fn unsigned_word_array_field_contracts_decay_to_typed_addresses() {
    let source = "struct packet { uint32 values[4]; }; uint32 read(struct packet* p, int32 k) { return p->values[k]; }";
    let proof = r#"verifying "fields.c";
        uint32 read(struct packet* p, int32 k) {
            requires 0 <= k and k < 4;
            views p->values[0..4];
            ensures result == old(p->values[k]);
        }"#;
    verify_c_sources(proof, &[("fields.c", source)]).unwrap();
    assert!(
        verify_c_sources(
            &proof.replace("views p->values[0..4];", ""),
            &[("fields.c", source)]
        )
        .is_err()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_00")]
fn modular_exceptional_call_continues_through_a_normal_assignment() {
    let c_source = r#"
        int32 helper(int32 x) { return x; }
        int32 caller(int32 x) {
            int32 y = helper(x);
            y = x;
            return y;
        }
    "#;
    let click_source = r#"
        verifying "calls.c";
        int32 helper(int32 x) throws int32 {
            ensures result == x;
            exceptional ensures exception == 7;
        }
        int32 caller(int32 x) throws int32 {
            ensures result == x;
            exceptional ensures exception == 7;
        }
    "#;
    verify_c_sources(click_source, &[("calls.c", c_source)])
        .expect("the normal call successor must continue while its throw successor exits");
    let expanded = expand_c_claim_source(
        click_source,
        &[("calls.c", c_source)],
        "caller",
        ContractProofClaim::ExceptionalEnsure(0),
    )
    .expect("the exceptional caller claim must expand across the call fork");
    verify_c_sources(&expanded, &[("calls.c", c_source)])
        .expect("the expanded call fork must reverify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_01")]
fn successive_modular_exceptional_calls_keep_each_throw_path() {
    let c_source = r#"
        int32 helper(int32 x) { return x; }
        int32 caller(int32 x) {
            int32 y = helper(x);
            y = helper(y);
            return y;
        }
    "#;
    let click_source = r#"
        verifying "calls.c";
        int32 helper(int32 x) throws int32 {
            ensures result == x;
            exceptional ensures exception == 7;
        }
        int32 caller(int32 x) throws int32 {
            ensures result == x;
            exceptional ensures exception == 7;
        }
    "#;
    verify_c_sources(click_source, &[("calls.c", c_source)])
        .expect("both call sites must retain their exceptional paths");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_01")]
fn exceptional_call_before_a_normal_branch_retains_its_exit() {
    let c_source = r#"
        int32 helper(int32 x) { return x; }
        int32 caller(int32 x, int32 flag) {
            int32 y = helper(x);
            if (flag) { y = x; } else { y = x; }
            return y;
        }
    "#;
    let click_source = r#"
        verifying "calls.c";
        int32 helper(int32 x) throws int32 {
            ensures result == x;
            exceptional ensures exception == 7;
        }
        int32 caller(int32 x, int32 flag) throws int32 {
            ensures result == x;
            exceptional ensures exception == 7;
        }
    "#;
    verify_c_sources(click_source, &[("calls.c", c_source)])
        .expect("a later normal branch must not drop the call's throw exit");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_01")]
fn exceptional_call_before_two_returning_normal_arms_retains_its_exit() {
    let c_source = r#"
        int32 helper(int32 x) { return x; }
        int32 caller(int32 x, int32 flag) {
            int32 y = helper(x);
            if (flag) { return y; } else { return x; }
        }
    "#;
    let click_source = r#"
        verifying "calls.c";
        int32 helper(int32 x) throws int32 {
            ensures result == x;
            exceptional ensures exception == 7;
        }
        int32 caller(int32 x, int32 flag) throws int32 {
            ensures result == x;
            exceptional ensures exception == 7;
        }
    "#;
    verify_c_sources(click_source, &[("calls.c", c_source)])
        .expect("a checked branch join must retain the earlier exceptional exit");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_01")]
fn nonterminal_exceptional_call_rejects_a_false_caller_claim() {
    let c_source = r#"
        int32 helper(int32 x) { return x; }
        int32 caller(int32 x) {
            int32 y = helper(x);
            y = x;
            return y;
        }
    "#;
    let click_source = r#"
        verifying "calls.c";
        int32 helper(int32 x) throws int32 {
            ensures result == x;
            exceptional ensures exception == 7;
        }
        int32 caller(int32 x) throws int32 {
            ensures result == x;
            exceptional ensures exception == 8;
        }
    "#;
    let error = verify_c_sources(click_source, &[("calls.c", c_source)])
        .expect_err("the normal continuation must not contaminate the throw claim");
    assert!(
        error.message().contains("exceptional_ensures_0"),
        "unexpected error: {error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_02")]
fn nonterminal_call_cannot_drop_an_unconstrained_exception() {
    let c_source = r#"
        int32 helper(int32 x) { return x; }
        int32 caller(int32 x) {
            int32 y = helper(x);
            y = x;
            return y;
        }
    "#;
    let click_source = r#"
        verifying "calls.c";
        int32 helper(int32 x) throws int32 {
            ensures result == x;
        }
        int32 caller(int32 x) {
            ensures result == x;
        }
    "#;
    let error = verify_c_sources(click_source, &[("calls.c", c_source)])
        .expect_err("the caller's omitted throws clause cannot hide the callee's throw");
    assert!(
        error.message().contains("caller"),
        "unexpected error: {error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_02")]
fn modular_exceptional_call_completes_both_caller_claim_families() {
    let c_source = r#"
        int32 helper(int32 x) { return x; }
        int32 caller(int32 x) { return helper(x); }
    "#;
    let click_source = r#"
        verifying "calls.c";
        int32 helper(int32 x) throws int32 {
            ensures result == x;
            exceptional ensures exception == 7;
        }
        int32 caller(int32 x) throws int32 {
            ensures result == x;
            exceptional ensures exception == 7;
        }
    "#;
    let verified = verify_c_sources(click_source, &[("calls.c", c_source)])
        .expect("normal and exceptional caller claims must verify");
    let exceptional = verified
        .iter()
        .filter(|theorem| {
            matches!(theorem.claim, VerifiedClaim::ExceptionalEnsure { .. })
                && matches!(
                    theorem.specification.outcome(),
                    FunctionOutcome::Throw { .. }
                )
        })
        .collect::<Vec<_>>();
    assert!(!exceptional.is_empty());
    assert!(
        exceptional
            .iter()
            .all(|theorem| theorem.checked_proposition.is_some()),
        "exceptional claims retain their proposition completion through certification"
    );
    let expanded = expand_c_claim_source(
        click_source,
        &[("calls.c", c_source)],
        "caller",
        ContractProofClaim::ExceptionalEnsure(0),
    )
    .expect("the caller's exceptional claim must expand");
    verify_c_sources(&expanded, &[("calls.c", c_source)])
        .expect("the expanded exceptional caller proof must verify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_02")]
fn modular_exceptional_call_rejects_a_false_caller_claim() {
    let c_source = r#"
        int32 helper(int32 x) { return x; }
        int32 caller(int32 x) { return helper(x); }
    "#;
    let click_source = r#"
        verifying "calls.c";
        int32 helper(int32 x) throws int32 {
            ensures result == x;
            exceptional ensures exception == 7;
        }
        int32 caller(int32 x) throws int32 {
            ensures result == x;
            exceptional ensures exception == 8;
        }
    "#;
    let error = verify_c_sources(click_source, &[("calls.c", c_source)])
        .expect_err("the callee's exceptional fact cannot prove a false caller claim");
    assert!(
        error.message().contains("exceptional_ensures_0"),
        "unexpected error: {error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_02")]
fn targeted_exceptional_caller_assumes_but_does_not_certify_an_unselected_callee() {
    let c_source = r#"
        int32 helper(int32 x) { return x + 1; }
        int32 caller(int32 x) { return helper(x); }
    "#;
    let click_source = r#"
        verifying "calls.c";
        int32 helper(int32 x) throws int32 {
            ensures result == x;
            exceptional ensures exception == 7;
        }
        int32 caller(int32 x) throws int32 {
            ensures result == x;
            exceptional ensures exception == 7;
        }
    "#;
    let expanded = expand_c_claim_source(
        click_source,
        &[("calls.c", c_source)],
        "caller",
        ContractProofClaim::ExceptionalEnsure(0),
    )
    .expect("targeted expansion may assume the callee interface");
    let error = verify_c_sources(&expanded, &[("calls.c", c_source)])
        .expect_err("whole-file verification must still certify the callee body");
    // The callee's two omitted proofs share its implicit grouped proof.
    assert!(
        error.message().contains("helper.contract"),
        "unexpected error: {error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_03")]
fn exceptional_contracts_publish_distinct_claim_families() {
    let c_source = r#"
            int32 helper(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "helper.c";

            int32 helper(int32 x) throws int32 {
                ensures result == x;
                exceptional ensures exception == 7;
            }
        "#;

    let verified = verify_c_sources(click_source, &[("helper.c", c_source)])
        .expect("a nonthrowing body should vacuously certify its exceptional family");
    assert!(
        verified
            .iter()
            .any(|theorem| matches!(&theorem.claim, VerifiedClaim::Ensure { .. }))
    );
    assert!(
        verified
            .iter()
            .any(|theorem| matches!(&theorem.claim, VerifiedClaim::ExceptionalEnsure { .. }))
    );
    let expanded = expand_c_claim_source(
        click_source,
        &[("helper.c", c_source)],
        "helper",
        ContractProofClaim::ExceptionalEnsure(0),
    )
    .expect("the exceptional claim should have an independently expandable proof site");
    verify_c_sources(&expanded, &[("helper.c", c_source)])
        .expect("the expanded exceptional claim should reverify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_03")]
fn exceptional_contract_bindings_are_family_specific() {
    let c_source = "int32 identity(int32 x) { return x; }";
    for (source, expected) in [
        (
            r#"
                verifying "identity.c";
                int32 identity(int32 x) {
                    exceptional ensures exception == 7;
                }
            "#,
            "requires `throws`",
        ),
        (
            r#"
                verifying "identity.c";
                int32 identity(int32 x) throws int32 {
                    exceptional ensures result == x;
                }
            "#,
            "`result` is not available",
        ),
        (
            r#"
                verifying "identity.c";
                int32 identity(int32 x) throws int32 {
                    ensures exception == 7;
                }
            "#,
            "`exception` is available only",
        ),
        (
            r#"
                verifying "identity.c";
                int32 identity(int32 x) throws uint32 {
                    ensures result == x;
                }
            "#,
            "exceptional payload",
        ),
        (
            r#"
                abstract resource token(x: int32);
                verifying "identity.c";
                int32 identity(int32 x) throws int32 {
                    owns token(x);
                    exceptional ensures exception == 7;
                }
            "#,
            "not resource transitions",
        ),
    ] {
        let error = verify_c_sources(source, &[("identity.c", c_source)])
            .expect_err("invalid exceptional surface contract must be rejected");
        assert!(
            error.message().contains(expected),
            "unexpected error: {error:?}"
        );
    }

    let external = r#"
        extern int32 identity(int32 x) throws int32 {
            exceptional ensures exception == 7;
        }
    "#;
    verify_c_sources(external, &[])
        .unwrap_or_else(|error| panic!("an external contract may throw: {error:?}"));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_03")]
fn abstract_resource_construction_adds_one_authorized_token() {
    let c_source = r#"
            int32 open_thing() {
                return 7;
            }
        "#;
    let click_source = r#"
            abstract resource open_fd(fd: int32);

            verifying "open_thing.c";

            int32 open_thing() {
                constructs open_fd(result);
                produces open_fd(result) by {
                    step_until(function.exit);
                    fold(open_fd(result));
                }
            }
        "#;

    verify_c_sources(click_source, &[("open_thing.c", c_source)])
        .expect("an authorized abstract resource construction should verify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_03")]
fn abstract_resource_construction_requires_function_authorization() {
    let c_source = r#"
            int32 fake_open() {
                return 7;
            }
        "#;
    let click_source = r#"
            abstract resource open_fd(fd: int32);

            verifying "fake_open.c";

            int32 fake_open() {
                produces open_fd(result) by {
                    step_until(function.exit);
                    fold(open_fd(result));
                }
            }
        "#;

    let error = verify_c_sources(click_source, &[("fake_open.c", c_source)])
        .expect_err("an unauthorized abstract resource construction must fail");
    assert!(
        error
            .message
            .contains("resource construction is not authorized"),
        "unexpected error: {error:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_03")]
fn closing_constructs_only_a_missing_authorized_output_token() {
    let inputs = [("identity.c", "int32 identity(int32 n) { return n; }")];
    let source = r#"
        abstract resource token(n: int32);
        verifying "identity.c";
        int32 identity(int32 n) {
            constructs token(result);
            produces token(result);
        } by { step_until(function.exit); }
    "#;
    let verified = verify_c_sources(source, &inputs).unwrap();
    let expanded = expand_checked_grouped_claim(source, &verified, "identity").unwrap();
    assert_eq!(
        expanded.matches("fold(token(result));").count(),
        1,
        "{expanded}"
    );
    without_implicit_solve(|| verify_c_sources(&expanded, &inputs)).unwrap();

    for individual_proof in [
        "produces token(result) by { step_until(function.exit); }",
        "produces token(result) by { step_until(function.exit); close(); }",
    ] {
        let individual = source
            .replace("produces token(result);", individual_proof)
            .replace("} by { step_until(function.exit); }", "}");
        let verified = verify_c_sources(&individual, &inputs).unwrap();
        let expanded =
            expand_checked_function_claim(&individual, &verified, "identity.produces_0").unwrap();
        assert_eq!(
            expanded.matches("fold(token(result));").count(),
            1,
            "{expanded}"
        );
        without_implicit_solve(|| verify_c_sources(&expanded, &inputs)).unwrap();
    }

    let held = source.replace(
        "constructs token(result);",
        "consumes token(n); constructs token(result);",
    );
    let verified = verify_c_sources(&held, &inputs).unwrap();
    let expanded = expand_checked_grouped_claim(&held, &verified, "identity").unwrap();
    assert!(!expanded.contains("fold("), "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, &inputs)).unwrap();

    for authorization in ["", "constructs token(7);"] {
        let unauthorized = source.replace("constructs token(result);", authorization);
        assert!(
            verify_c_sources(&unauthorized, &inputs).is_err(),
            "{unauthorized}"
        );
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_04")]
fn contradiction_closes_an_impossible_concrete_outcome() {
    let c_source = r#"
            int32 always_zero(int32* data) {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "always_zero.c";

            int32 always_zero(int32* data) {
                ensures result == 1 implies data[0] == 2;
            } by {
                step();
                have result == 1 implies data[0] == 2 by {
                    intro();
                    contradiction(result == 1);
                }
                close();
            }
        "#;

    verify_c_sources(click_source, &[("always_zero.c", c_source)]).expect(
        "a concrete-false outcome guard should avoid lowering its unavailable memory consequent",
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_04")]
fn flat_function_proof_stays_on_proof_through_claim_acceptance() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures returns_x: result == x;
            }
        "#;

    let (verified, flat_units) = proof::count_flat_proof_units(|| {
        verify_c_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("the flat function proof should verify");
    assert_eq!(
        flat_units, 1,
        "the claim should finish from one retained Proof"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_04")]
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
                    with(marker(x)) {
                        step_until(function.exit);
                    }
                    close();
                }
            }
        "#;

    let (verified, flat_units) = proof::count_flat_proof_units(|| {
        verify_c_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("the individual open proof should verify");
    assert_eq!(flat_units, 1, "the open claim should finish from one Proof");

    let expanded = expand_c_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        ContractProofClaim::Ensure(0),
    )
    .expect("the individual open proof should expand");
    assert!(expanded.contains("with(marker(x))"), "{expanded}");
    assert!(
        !expanded.contains("step_until(function.exit);"),
        "{expanded}"
    );
    verify_c_sources(&expanded, &[("identity.c", c_source)])
        .expect("the rewritten individual open proof should verify normally");

    let checked_step = "                        step();\n";
    let corrupted = expanded.replacen(checked_step, "", 1);
    assert_ne!(
        corrupted, expanded,
        "expansion should expose the return step"
    );
    verify_c_sources(&corrupted, &[("identity.c", c_source)])
        .expect_err("removing the scoped return step must invalidate the rewritten proof");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
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
                owns allocation(owner->data, 4);
                owns owner->data[0..1];
            }

            verifying "replace_allocated_cell.c";
            verifying "replace_after_scoped_open.c";

            int32 replace_allocated_cell(struct cell_owner* owner) {
                owns allocated_cell(owner);

                ensures result == 0 or result == 1;
                ensures result == 0 implies owner->data == old(owner->data);
            } by {
                unfold(allocated_cell(owner));
                // Declare both pointers, save the old cell, and allocate its replacement.
                step(); step(); step(); step();
                branch { true => { step(); } false => { } }
                step_until(function.exit);
                fold(allocated_cell(owner));
                close();
            }

            int32 replace_after_scoped_open(struct cell_owner* owner) {
                owns allocated_cell(owner);

                ensures result == 0 or result == 1;
            } by {
                with(allocated_cell(owner)) {
                }
                step();
                step();
                if at(region(1).exit, owner->data) == old(owner->data) {
                    step();
                } else {
                    step();
                }
                step_until(function.exit);
                close();
            }
        "#;
    let sources = &[
        ("replace_allocated_cell.c", replace_source),
        ("replace_after_scoped_open.c", caller_source),
    ];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c_sources(click_source, sources));
    verified.expect("the explicit call partition should remain on one retained Proof");
    assert_eq!(
        flat_units, 2,
        "both source proofs should enter the direct Proof driver"
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
                owns allocation(owner->data, 4);
                owns owner->data[0..1];
            }

            verifying "replace_allocated_cell.c";
            verifying "replace_then_branch.c";

            int32 replace_allocated_cell(struct cell_owner* owner) {
                owns allocated_cell(owner);

                ensures result == 0 or result == 1;
                ensures result == 0 implies owner->data == old(owner->data);
                ensures owner->data == old(owner->data) implies result == 0;
                ensures result == 1 implies not owner->data == old(owner->data);
            } by {
                unfold(allocated_cell(owner));
                // Declare both pointers, save the old cell, and allocate its replacement.
                step(); step(); step(); step();
                branch { true => { step(); } false => { } }
                step_until(function.exit);
                fold(allocated_cell(owner));
                close();
            }

            int32 replace_then_branch(struct cell_owner* owner) {
                owns allocated_cell(owner);

                ensures result == 0 or result == 1;
            } by {
                with(allocated_cell(owner)) {
                }
                step();
                step();
                step();
                if program::replaced == 0 {
                    step();
                    step();
                } else {
                    step();
                    step();
                }
                close();
            }
        "#;

    (replace_source, caller_source, click_source)
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.8s in the parallel gate"]
fn explicit_proof_if_does_not_capture_shared_following_c_if() {
    let (replace_source, caller_source, click_source) = result_case_split_sources();
    let click_source = click_source.replace(
        "                if program::replaced == 0 {",
        "                if at(region(1).exit, owner->data) == old(owner->data) {\n                } else {\n                }\n                if program::replaced == 0 {",
    );
    assert!(
        click_source.contains("if at(region(1).exit, owner->data)"),
        "the regression must insert the empty explicit proof split"
    );
    verify_c_sources(
        &click_source,
        &[
            ("replace_allocated_cell.c", replace_source),
            ("replace_then_branch.c", caller_source),
        ],
    )
    .expect("the shared following C `if` must perform its own explicit split");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn following_c_if_splits_one_symbolic_call_successor() {
    let (replace_source, caller_source, click_source) = result_case_split_sources();
    let sources = &[
        ("replace_allocated_cell.c", replace_source),
        ("replace_then_branch.c", caller_source),
    ];

    verify_c_sources(click_source, sources)
        .expect("the following C `if` should split the symbolic call successor");
    let expanded = expand_c_claim_source(
        click_source,
        sources,
        "replace_then_branch",
        ContractProofClaim::Grouped,
    )
    .expect("the explicit result split should retain an expandable proof");
    verify_c_sources(&expanded, sources)
        .expect("the explicit result split expansion should check independently");

    // The call has one symbolic successor. Its data-identity postconditions
    // are irrelevant to the following C `if`, which branches only on the
    // returned value and therefore must not need evidence to collapse hidden
    // call-successor lanes.
    let without_identity_bridge = click_source
        .replace(
            "                ensures result == 0 implies owner->data == old(owner->data);\n",
            "",
        )
        .replace(
            "                ensures owner->data == old(owner->data) implies result == 0;\n",
            "",
        );
    assert_ne!(
        without_identity_bridge, click_source,
        "the bridging postconditions should be present"
    );
    verify_c_sources(&without_identity_bridge, sources)
        .expect("the C `if` must not depend on unrelated call identity facts");
    let expanded_without_bridge = expand_c_claim_source(
        &without_identity_bridge,
        sources,
        "replace_then_branch",
        ContractProofClaim::Grouped,
    )
    .expect("the single-successor proof should remain expandable");
    verify_c_sources(&expanded_without_bridge, sources)
        .expect("the expanded single-successor proof should check independently");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_04")]
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
                ensures result == x;
            } by {
                step();
                if x >= 0 {
                    step();
                    step();
                } else {
                    step();
                    step();
                }
                close();
            }
    "#;
    let sources = &[("identity_after_prefix.c", c_source)];

    let _ = crate::kernel::take_checked_function_body_execution_count();
    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c_sources(click_source, sources));
    verified.expect("the mid-execution proof case split should remain on one retained Proof");
    assert_eq!(flat_units, 1, "the contract should retain one Proof");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "an exhaustive proof-level case split should complete its retained execution paths"
    );

    let expanded = expand_c_claim_source(
        click_source,
        sources,
        "identity_after_prefix",
        ContractProofClaim::Grouped,
    )
    .expect("the retained mid-execution case split should expand");
    assert!(expanded.contains("if x >= 0"), "{expanded}");
    verify_c_sources(&expanded, sources)
        .expect("the expanded mid-execution case split should verify independently");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_05")]
fn post_execution_resource_fold_completes_without_a_body_rerun() {
    let c_source = r#"
        int32 preserve_cell(int32 p[]) {
            return p[0];
        }
    "#;
    let click_source = r#"
        resource cell(p: int32*) {
            owns p[0..1];
        }

        verifying "preserve_cell.c";

        int32 preserve_cell(int32 p[]) {
            owns cell(p);
            ensures result == old(p[0]);
        } by {
            unfold(cell(p));
            step_until(function.exit);
            fold(cell(p));
            close();
        }
    "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c_sources(click_source, &[("preserve_cell.c", c_source)])
        .expect("the post-execution resource fold should verify");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "a checked post-execution resource fold should not force a whole-body rerun"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_05")]
fn implicitly_closed_population_entry_completes_without_a_body_rerun() {
    let c_source = r#"
        int32 inspect_counts(void* p, void* q) {
            return 0;
        }
    "#;
    let click_source = r#"
        authorized resource checked_out(pool: void*) {}

        verifying "inspect_counts.c";

        int32 inspect_counts(void* p, void* q) {
            requires p != q;
            owns authority(checked_out(p));
            owns authority(checked_out(q));
            requires count(checked_out(p)) == 2;
            requires count(checked_out(q)) == 1;
            owns checked_out(p);
            owns checked_out(p);
            owns checked_out(q);

            ensures count(checked_out(p)) == 2;
            ensures count(checked_out(q)) == 1;
            ensures result == 0;
        }
    "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c_sources(click_source, &[("inspect_counts.c", c_source)])
        .expect("populations closed by the outcome solve should verify");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "the completed path applies the contract exit rule, so no explicit frame is needed"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_05")]
fn callee_subrange_requirement_completes_without_a_body_rerun() {
    let write_at = r#"
        int32 write_at(int32 p[], int32 i) {
            p[i] = 1;
            return p[i];
        }
    "#;
    let caller = r#"
        int32 write_at_symbolic(int32 p[], int32 i, int32 n) {
            int32 value;
            value = write_at(p, i);
            return value;
        }
    "#;
    let click_source = r#"
        verifying "write_at.c";
        verifying "write_at_symbolic.c";

        int32 write_at(int32 p[], int32 i) {
            requires i >= 0;
            requires i < 2147483647;
            owns p[i..i + 1];

        }

        int32 write_at_symbolic(int32 p[], int32 i, int32 n) {
            requires i >= 0;
            requires i < n;
            requires n <= 2147483647;
            owns p[0..n];

        }
    "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c_sources(
        click_source,
        &[("write_at.c", write_at), ("write_at_symbolic.c", caller)],
    )
    .expect("a callee requirement inside the caller's viewable range should verify");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "the callee's viewability premise is covered by the caller's retained viewable range"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_05")]
fn token_quantity_entry_completes_without_a_body_rerun() {
    let c_source = "int32 preserve(int32 x) { return x; }";
    let click_source = r#"
        abstract resource marker(x: int32);

        verifying "preserve.c";

        int32 preserve(int32 x) {
            owns 2 of marker(x);
            ensures result == x;
        } by {
            step();
            close();
        }
    "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c_sources(click_source, &[("preserve.c", c_source)])
        .expect("the token quantity entry should verify");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "token quantity entry normalization should not rerun the C body"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_06")]
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
            }
        "#;

    let (verified, flat_units) = proof::count_flat_proof_units(|| {
        verify_c_sources(click_source, &[("identity.c", c_source)])
    });
    let verified = verified.expect("the grouped flat function proof should verify");
    assert_eq!(verified.len(), 2, "both grouped claims should be proved");
    assert_eq!(
        flat_units, 1,
        "the grouped claims should finish from one retained Proof"
    );

    let expanded = expand_c_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        ContractProofClaim::Grouped,
    )
    .expect("the retained grouped Proof should expand");
    assert!(
        !expanded.contains("step_until(function.exit);"),
        "{expanded}"
    );
    assert!(!expanded.contains("solve();"), "{expanded}");
    verify_c_sources(&expanded, &[("identity.c", c_source)])
        .expect("the grouped rewrite should verify normally");

    let corrupted = expanded.replacen("have result == result", "have result != result", 1);
    assert_ne!(
        corrupted, expanded,
        "grouped expansion should expose a checked have"
    );
    verify_c_sources(&corrupted, &[("identity.c", c_source)])
        .expect_err("tampering with a grouped extracted operation must invalidate the proof");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_06")]
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
            }
        "#;

    let (verified, flat_units) = proof::count_flat_proof_units(|| {
        verify_c_sources(click_source, &[("classify.c", c_source)])
    });
    let verified = verified.expect("the grouped N-way function proof should verify");
    assert_eq!(
        verified.len(),
        6,
        "both claims should be proved on each of the three outcomes"
    );
    assert_eq!(flat_units, 1, "all outcomes should stay on one Proof");

    let expanded = expand_c_claim_source(
        click_source,
        &[("classify.c", c_source)],
        "classify",
        ContractProofClaim::Grouped,
    )
    .expect("the retained grouped N-way Proof should expand");
    assert!(
        !expanded.contains("step_until(function.exit);"),
        "{expanded}"
    );
    assert!(!expanded.contains("solve();"), "{expanded}");
    verify_c_sources(&expanded, &[("classify.c", c_source)])
        .expect("the expanded grouped N-way proof should verify normally");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_06")]
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
                step_until(function.exit);
                close();
            }
        "#;

    let (verified, flat_units) = proof::count_flat_proof_units(|| {
        verify_c_sources(click_source, &[("pointer_is_null.c", c_source)])
    });
    let verified = verified.expect("the feasible grouped outcome should verify");
    assert_eq!(verified.len(), 1);
    assert_eq!(flat_units, 1, "the selected outcome should stay on Proof");

    let expanded = expand_c_claim_source(
        click_source,
        &[("pointer_is_null.c", c_source)],
        "pointer_is_null",
        ContractProofClaim::Grouped,
    )
    .expect("the feasible grouped outcome should expand");
    verify_c_sources(&expanded, &[("pointer_is_null.c", c_source)])
        .expect("the rewritten feasible-outcome proof should verify normally");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_06")]
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
                ensures data[0] == 1;
            }

            int32 call_set_one(int32 data[], int32 permit) {
                requires permit >= 1;
                owns data[0..1];
                ensures exact: result == 1;
                ensures post_call: data[0] == 1;
            }
        "#;
    let sources = &[("set_one.c", set_source), ("call_set_one.c", caller_source)];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c_sources(click_source, sources));
    verified.expect("the grouped call and callee proofs should verify");
    assert_eq!(flat_units, 2, "both functions should retain one Proof");

    let expanded = expand_c_claim_source(
        click_source,
        sources,
        "call_set_one",
        ContractProofClaim::Grouped,
    )
    .expect("the retained grouped call Proof should expand");
    let caller_expansion = expanded
        .split("int32 call_set_one")
        .nth(1)
        .expect("the expanded source should retain the selected caller");
    assert!(
        !caller_expansion.contains("step_until(function.exit);"),
        "{expanded}"
    );
    assert!(!caller_expansion.contains("solve();"), "{expanded}");
    assert!(caller_expansion.contains("step();"), "{expanded}");
    verify_c_sources(&expanded, sources)
        .expect("the rewritten grouped call proof should verify normally");

    // The call step runs in the caller's context; its prerequisite is the
    // caller's requirement, and removing that requirement invalidates it.
    let corrupted = expanded.replacen("requires permit >= 1;", "", 1);
    assert_ne!(
        corrupted, expanded,
        "the caller's requirement should be present"
    );
    verify_c_sources(&corrupted, sources)
        .expect_err("removing the call prerequisite from the context must invalidate the proof");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn outcome_solve_spells_a_call_postcondition_across_two_states() {
    // `touch` may write both fields and certifies `p->x == old(p->x)`: after
    // each call the caller's `p->x` is a fresh cell related to its previous
    // value only by that certified fact, and no single frontier position
    // denotes both operands. Two calls make the caller's outcome a chain of
    // two such facts, so the outcome `solve` must cite them as premises,
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
                ensures p->x == old(p->x);
                ensures p->y == 1;
            }

            int32 keep_x(struct pair* p) {
                requires p != 0;
                owns p->x;
                owns p->y;
                ensures result == old(p->x);
            }
        "#;
    let struct_source = "struct pair { int32 x; int32 y; };\n";
    let touch_source = format!("{struct_source}{touch_source}");
    let keep_source = format!("{struct_source}{keep_source}");
    let sources = &[
        ("touch.c", touch_source.as_str()),
        ("keep_x.c", keep_source.as_str()),
    ];

    let (verified, planning_transitions) =
        collect_planning_statement_transitions(|| verify_c_sources(click_source, sources));
    verified.expect("the caller should verify through the checked linear search");
    assert!(
        planning_transitions.is_empty(),
        "the caller's outcome must close without planner construction: {planning_transitions:#?}"
    );

    let expanded =
        expand_c_claim_source(click_source, sources, "keep_x", ContractProofClaim::Grouped)
            .expect("the retained caller Proof should expand");
    let caller_expansion = expanded
        .split("int32 keep_x")
        .nth(1)
        .expect("the expanded source should retain the caller");
    // The checked frame equation connects the states in the shared graph.
    assert!(caller_expansion.contains("close();"), "{expanded}");
    verify_c_sources(&expanded, sources)
        .expect("the rewritten caller proof should verify normally");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_07")]
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
                owns token(key);
            }

            verifying "borrow_token.c";
            verifying "borrow_token_twice.c";

            int32 borrow_token(int32 key) {
                owns token_bundle(key);
                ensures result == key;
            }

            int32 borrow_token_twice(int32 key) {
                owns token_bundle(key);
                ensures result == key;
            }
        "#;
    let sources = &[
        ("borrow_token.c", borrow_source),
        ("borrow_token_twice.c", caller_source),
    ];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c_sources(click_source, sources));
    verified.expect("declared composite resources should cross both checked calls");
    assert_eq!(flat_units, 2, "both functions should retain one Proof");

    let expanded = expand_c_claim_source(
        click_source,
        sources,
        "borrow_token_twice",
        ContractProofClaim::Grouped,
    )
    .expect("the retained declared-resource call Proof should expand");
    let caller_expansion = expanded
        .split("int32 borrow_token_twice")
        .nth(1)
        .expect("the expanded source should retain the selected caller");
    assert!(
        !caller_expansion.contains("step_until(function.exit);"),
        "{expanded}"
    );
    assert!(!caller_expansion.contains("solve();"), "{expanded}");
    assert_eq!(
        caller_expansion.matches("step();").count(),
        6,
        "each call and assignment should retain its own checked step: {expanded}"
    );
    verify_c_sources(&expanded, sources)
        .expect("the rewritten declared-resource call proof should verify normally");

    let checked_step = "                step();\n";
    let corrupted = expanded.replacen(checked_step, "", 1);
    assert_ne!(
        corrupted, expanded,
        "expansion should expose checked call steps"
    );
    verify_c_sources(&corrupted, sources)
        .expect_err("removing an extracted resource-bearing step must invalidate the proof");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
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
                owns owned_cell(cell);
            }

            verifying "set_seven.c";
            verifying "set_wrapped_seven.c";

            int32 set_seven(int32* cell) {
                owns owned_cell(cell);
                ensures result == 7;
            } by {
                with(owned_cell(cell)) {
                    step_until(function.exit);
                }
                close();
            }

            int32 set_wrapped_seven(int32* cell) {
                owns wrapped_cell(cell);
                ensures result == 7;
            } by {
                with(wrapped_cell(cell)) {
                    step_until(function.exit);
                }
                close();
            }
        "#;
    let sources = &[
        ("set_seven.c", set_source),
        ("set_wrapped_seven.c", caller_source),
    ];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c_sources(click_source, sources));
    verified.expect("mutable composite resources should cross the scoped opaque call");
    assert_eq!(flat_units, 2, "both open-scope proofs should stay on Proof");

    let expanded = expand_c_claim_source(
        click_source,
        sources,
        "set_wrapped_seven",
        ContractProofClaim::Grouped,
    )
    .expect("the retained mutable composite call scope should expand");
    let caller_expansion = expanded
        .split("int32 set_wrapped_seven")
        .nth(1)
        .expect("the expanded source should retain the selected caller");
    assert!(
        caller_expansion.contains("with(wrapped_cell(cell))"),
        "{expanded}"
    );
    assert!(
        !caller_expansion.contains("step_until(function.exit);"),
        "{expanded}"
    );
    assert!(!caller_expansion.contains("solve();"), "{expanded}");
    verify_c_sources(&expanded, sources)
        .expect("the rewritten scoped composite-call proof should verify normally");

    let checked_step = "                    step();\n";
    let corrupted = expanded.replacen(checked_step, "", 1);
    assert_ne!(
        corrupted, expanded,
        "expansion should expose a scoped call step"
    );
    verify_c_sources(&corrupted, sources)
        .expect_err("removing the scoped call step must invalidate the rewritten proof");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
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
                owns owned_cell(cell);
            }

            verifying "set_seven.c";
            verifying "prepare_then_set_seven.c";

            int32 set_seven(int32* cell, int32 choose) {
                owns owned_cell(cell);
                ensures result == 0 or result == 1;
            } by {
                with(owned_cell(cell)) {
                    branch { true => { step(); } false => { } }
                    step_until(function.exit);
                }
                close();
            }

            int32 prepare_then_set_seven(int32* cell, int32 choose) {
                owns wrapped_cell(cell);
                ensures result == 0 or result == 1;
            } by {
                with(wrapped_cell(cell)) {
                }
                step_until(function.exit);
                close();
            }
        "#;
    let sources = &[
        ("set_seven.c", set_source),
        ("prepare_then_set_seven.c", caller_source),
    ];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c_sources(click_source, sources));
    verified.expect("the closed preparatory scope should continue through the checked call");
    assert_eq!(flat_units, 2, "both functions should retain one Proof");

    let expanded = expand_c_claim_source(
        click_source,
        sources,
        "prepare_then_set_seven",
        ContractProofClaim::Grouped,
    )
    .expect("the retained preparatory scope Proof should expand");
    let caller_expansion = expanded
        .split("int32 prepare_then_set_seven")
        .nth(1)
        .expect("the expanded source should retain the selected caller");
    assert!(
        !caller_expansion.contains("step_until(function.exit);"),
        "{expanded}"
    );
    assert!(!caller_expansion.contains("solve();"), "{expanded}");
    assert!(caller_expansion.contains("with(wrapped_cell(cell))"));
    verify_c_sources(&expanded, sources)
        .unwrap_or_else(|error| panic!("TEMP {error:?}\n{expanded}"));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_07")]
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
                ensures result == (x + 1) + 1;
            } by {
                with(first_marker(x)) {
                    step();
                }
                with(second_marker(x)) {
                    step_until(function.exit);
                }
                close();
            }
        "#;
    let sources = &[("add_twice.c", c_source)];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c_sources(click_source, sources));
    verified.expect("both sequential scopes should advance one checked Proof");
    assert_eq!(flat_units, 1, "the function should retain one Proof");

    let expanded = expand_c_claim_source(
        click_source,
        sources,
        "add_twice",
        ContractProofClaim::Grouped,
    )
    .expect("the retained sequential scopes should expand");
    let caller_expansion = expanded
        .split("int32 add_twice")
        .nth(1)
        .expect("the expanded source should retain the selected function");
    assert_eq!(
        caller_expansion.matches("with(").count(),
        2,
        "both top-level scopes should be serialized: {expanded}"
    );
    assert!(
        !caller_expansion.contains("step_until(function.exit);"),
        "{expanded}"
    );
    assert!(!caller_expansion.contains("solve();"), "{expanded}");
    verify_c_sources(&expanded, sources)
        .expect("the rewritten sequential-scope proof should verify normally");

    let checked_step = "                    step();\n";
    let corrupted = expanded.replacen(checked_step, "", 1);
    assert_ne!(
        corrupted, expanded,
        "expansion should expose both checked statements"
    );
    verify_c_sources(&corrupted, sources)
        .expect_err("removing one scoped statement must invalidate the rewritten proof");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_07")]
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
            }
        "#;
    let sources = &[("identity.c", c_source)];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c_sources(click_source, sources));
    let verified = verified.expect("the grouped predicate contract should verify");
    assert_eq!(verified.len(), 2, "both predicate claims should be proved");
    assert_eq!(
        flat_units, 1,
        "the predicate claims should stay on one Proof"
    );

    let expanded = expand_c_claim_source(
        click_source,
        sources,
        "identity",
        ContractProofClaim::Grouped,
    )
    .expect("the retained predicate Proof should expand");
    assert!(
        expanded.contains("have nonnegative(result) by {"),
        "{expanded}"
    );
    assert!(expanded.contains("unfold(same("), "{expanded}");
    assert!(
        !expanded.contains("step_until(function.exit);"),
        "{expanded}"
    );
    assert!(!expanded.contains("solve();"), "{expanded}");
    verify_c_sources(&expanded, sources)
        .expect("the rewritten predicate proof should verify normally");

    let corrupted = expanded.replacen("unfold(same(", "unfold(nonnegative(", 1);
    assert_ne!(
        corrupted, expanded,
        "expansion should expose the predicate unfold"
    );
    verify_c_sources(&corrupted, sources)
        .expect_err("tampering with the extracted predicate operation must fail");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_07")]
fn heap_backed_predicate_contract_stays_on_checked_proof() {
    let c_source = r#"
            int32 read_first(int32 p[2]) {
                return p[0];
            }
        "#;
    let click_source = r#"
            verifying "read_first.c";

            predicate ordered_pair(p: int32[2]) {
                p[0] <= p[1]
            }

            int32 read_first(int32 p[2]) {
                views p[0..2];
                requires ordered_pair(p);
                ensures result == p[0];
                ensures remains_ordered: ordered_pair(p);
            } by {
                step();
                close();
            }
        "#;

    let verified = { verify_c_sources(click_source, &[("read_first.c", c_source)]) };
    let verified = verified.expect("heap-backed predicate contract should verify");
    assert_eq!(verified.len(), 2);
    assert!(
        verified
            .iter()
            .all(|theorem| theorem.checked_proposition.is_some())
    );
    assert!(
        verified
            .iter()
            .all(|theorem| theorem.expanded_proof.is_some())
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_08")]
fn quantified_heap_scope_stays_on_checked_proof() {
    let c_source = r#"
            int32 read_first(int32 p[2]) {
                return p[0];
            }
        "#;
    let click_source = r#"
            verifying "read_first.c";

            int32 read_first(int32 p[2]) {
                views p[0..2];
                ensures result == p[0];
                ensures stable: forall (k: int32) {
                    0 <= k and k < 2 implies p[k] == p[k]
                };
            } by {
                step();
                have forall (k: int32) {
                    0 <= k and k < 2 implies p[k] == p[k]
                } by {
                    intro();
                    intro();
                    close();
                }
                close();
            }
        "#;

    let verified = { verify_c_sources(click_source, &[("read_first.c", c_source)]) };
    let verified = verified.expect("quantified heap scope should verify");
    assert_eq!(verified.len(), 2);
    assert!(
        verified
            .iter()
            .all(|theorem| theorem.checked_proposition.is_some())
    );
    assert!(
        verified
            .iter()
            .all(|theorem| theorem.expanded_proof.is_some())
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_08")]
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
                    close();
                }
                have separate(memory(left[0..1]), memory(right[0..1])) by {
                    close();
                }
                step_until(function.exit);
                close();
            }
        "#;
    let sources = &[("inspect_pair.c", c_source)];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c_sources(click_source, sources));
    verified.expect("leading resource relations should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");

    let expanded = expand_c_claim_source(
        click_source,
        sources,
        "inspect_pair",
        ContractProofClaim::Grouped,
    )
    .expect("the retained resource-relation scopes should expand");
    assert!(
        expanded.contains("have contains(pair(left, right)"),
        "{expanded}"
    );
    assert!(
        expanded.contains("have separate(memory(left[0..1])"),
        "{expanded}"
    );
    verify_c_sources(&expanded, sources)
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
        let corrupted_result = { verify_c_sources(&corrupted, sources) };
        corrupted_result.expect_err(&format!(
            "tampering with {relation} must invalidate the proof"
        ));
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
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
                ensures result == 0;
            } by {
                observe(pair(left, right));
                unfold(pair(left, right));
                have contains(pair(left, right), memory(left[0..1])) by {
                    close();
                }
                have separate(memory(left[0..1]), memory(right[0..1])) by {
                    close();
                }
                fold(pair(left, right));
                step_until(function.exit);
                close();
            }
        "#;
    let sources = &[("inspect_pair.c", c_source)];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c_sources(click_source, sources));
    verified.expect("relations projected by an explicit unfold should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");

    let expanded = expand_c_claim_source(
        click_source,
        sources,
        "inspect_pair",
        ContractProofClaim::Grouped,
    )
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
    verify_c_sources(&expanded, sources)
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
    let corrupted_result = { verify_c_sources(&corrupted, sources) };
    corrupted_result.expect_err("tampering with the derived separation must fail");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_08")]
fn grouped_owned_outcome_resources_stay_on_one_proof() {
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
                ensures result == 7;
            } by {
                unfold(seven_cell(cell));
                step_until(function.exit);
                have cell[0] == 7 by {
                    close();
                }
                fold(seven_cell(cell));
                close();
            }
        "#;
    let sources = &[("set_seven.c", c_source)];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c_sources(click_source, sources));
    verified.expect("owned outcome resource operations should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");

    let expanded = expand_c_claim_source(
        click_source,
        sources,
        "set_seven",
        ContractProofClaim::Grouped,
    )
    .expect("the retained owned outcome Proof should expand");
    assert!(expanded.contains("unfold(seven_cell(cell));"), "{expanded}");
    assert!(expanded.contains("have cell[0] == 7 by {"), "{expanded}");
    assert!(expanded.contains("fold(seven_cell(cell));"), "{expanded}");
    verify_c_sources(&expanded, sources)
        .expect("the rewritten owned outcome proof should verify normally");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_08")]
fn flat_function_expansion_rewrites_and_rejects_tampering() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures returns_x: result == x;
            }
        "#;

    let expanded = expand_c_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        ContractProofClaim::Ensure(0),
    )
    .expect("the retained flat Proof should expand");
    assert!(
        !expanded.contains("step_until(function.exit);"),
        "{expanded}"
    );
    assert!(!expanded.contains("solve();"), "{expanded}");
    verify_c_sources(&expanded, &[("identity.c", c_source)])
        .expect("the rewritten source should verify normally");

    let corrupted = expanded.replacen("have result == x", "have result != x", 1);
    assert_ne!(
        corrupted, expanded,
        "expansion should expose its checked have"
    );
    verify_c_sources(&corrupted, &[("identity.c", c_source)])
        .expect_err("tampering with an extracted operation must invalidate the source proof");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_09")]
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
                owns data[0..1];
                ensures data[0] == 0;
            } by {
                step_until(function.exit);
                have data[0] == 0 by {
                    close();
                }
                close();
            }
        "#;

    verify_c_sources(click_source, &[("clear_first.c", c_source)])
        .expect("frame premises should use facts established by preceding exit haves");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_09")]
fn ordinary_verification_stops_at_the_tactic_work_budget() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures returns_x: result == x;
            }
        "#;
    let limits = crate::instrumentation::TacticWorkLimits {
        simple: 0,
        smart: 0,
        control: 0,
    };
    let (result, events) = crate::instrumentation::collect(|| {
        crate::instrumentation::with_tactic_work_limits(limits, || {
            verify_c_sources(click_source, &[("identity.c", c_source)])
        })
    });
    let error = result.expect_err("the first tactic should exhaust its zero work budget");
    assert!(
        error.message().contains("deterministic") && error.message().contains("work budget"),
        "{error:?}"
    );
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
        !started.contains(&"solve"),
        "later tactics must not start after an exhausted budget: {started:?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_09")]
fn verifies_omitted_proof_with_default_prover() {
    let c_source = r#"
            int32 zero() {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "zero.c";

            int32 zero() {
                ensures returns_zero: result == 0;
            }
        "#;

    let verified = verify_c_sources(click_source, &[("zero.c", c_source)])
        .expect("omitted proof clauses should use the default prover");

    assert_eq!(verified.len(), 1);
    assert_eq!(verified[0].proof_kind(), ProofKind::TacticScript);
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_09")]
fn solve_rejects_loop_backed_claims() {
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
                ensures returns_three: result == 3 by close();
            }
        "#;

    let error = verify_c_sources(click_source, &[("count_to_three.c", c_source)])
        .expect_err("solve should not run loop verification");

    assert!(
        error
            .message()
            .contains("`close` closes the outcome claims at function exit and does not execute"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_10")]
fn verifies_memory_postcondition() {
    let source = FILL3_CLICK.replace(
        "ensures returns_second: result == 2",
        "ensures third: p[2] == 2",
    );
    let verified = verify_c_sources(&source, &[("fill3.c", FILL3_C)])
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_10")]
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
                requires viewable(p[0..2]);
                consumes p[1..2];
                ensures keeps_first_cell: forall (k: int32) {
                    0 <= k and k < 1 implies p[k] == old(p[k])
                };
            }
        "#;

    let verified = verify_c_sources(click_source, &[("write_second.c", c_source)])
        .expect("unwritten segment should match old memory");

    assert_eq!(verified.len(), 1);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
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
                consumes p[i..i + 1];
                views p[j..j + 1];
                requires separate(memory(p[i..i + 1]), memory(p[j..j + 1]));
                ensures keeps_j: result == old(p[j]);
            }
        "#;

    let verified = verify_c_sources(click_source, &[("write_i_read_j.c", c_source)])
        .expect("separate singleton ranges should prove symbolic unwritten read");

    assert_eq!(verified.len(), 1);

    let offset = click_source.find("ensures keeps_j").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c_tactic_source_at(
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
    verify_c_sources(&expanded, &[("write_i_read_j.c", c_source)])
        .expect("expanded unwritten read should check");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
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
                consumes p[1..2];
                ensures keeps_second_cell: forall (k: int32) {
                    1 <= k and k < 2 implies p[k] == old(p[k])
                };
            }
        "#;

    let error = verify_c_sources(click_source, &[("write_second.c", c_source)])
        .expect_err("overwritten segment should not match old memory");

    assert!(
        error.message().contains("goal:") && error.message().contains("recent premises"),
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
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_10")]
fn owned_segment_rejects_write_outside_owned_memory() {
    let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
    let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                consumes p[0..1];
                ensures returns_written: result == 9;
            }
        "#;

    let error = verify_c_sources(click_source, &[("write_second.c", c_source)])
        .expect_err("write outside owned memory should fail");

    assert!(
        error
            .message()
            .contains("missing resource fact `owns p[1]`"),
        "{}",
        error.message()
    );
    assert!(
        error.message().contains("resource facts: [owns p[0]]"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_10")]
fn sequence_contracts_reject_mixed_and_non_equality_types() {
    let c_source = r#"
        void inspect(int32* words, uint8_t* bytes) {}
    "#;
    let cases = [
        (
            "[words[0]] == [bytes[0]]",
            "sequence element types do not match",
        ),
        (
            "[words[0]] == words[0]",
            "sequence equality requires a sequence",
        ),
        (
            "[words[0]] < [words[0]]",
            "sequences support only `==` and `!=`",
        ),
    ];

    for (claim, expected) in cases {
        let click_source = format!(
            r#"
                verifying "inspect.c";

                void inspect(int32 words[], uint8 bytes[]) {{
                    ensures {claim};
                }}
            "#
        );
        let error = verify_c_sources(&click_source, &[("inspect.c", c_source)])
            .expect_err("ill-typed sequence contract should fail");
        assert!(
            error.message().contains(expected),
            "unexpected diagnostic for `{claim}`: {}",
            error.message()
        );
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_11")]
fn source_have_failures_keep_the_written_operation_in_each_execution_phase() {
    let c_source = "int32 identity(int32 x) { return x; }";
    for (before, after) in [
        ("", "step_until(function.exit);"),
        ("step_until(function.exit);", ""),
    ] {
        for (body, diagnostic) in [
            ("apply(missing()); close();", "unknown theorem `missing`"),
            ("unfold(missing(0)); close();", "missing"),
            ("step(); close();", "unsupported proof operation `step`"),
        ] {
            let source = format!(
                r#"
                verifying "identity.c";
                int32 identity(int32 x) {{
                    ensures result == x;
                }} by {{
                    {before}
                    have x == x by {{ {body} }}
                    {after}
                    close();
                }}
            "#
            );
            let error = verify_c_sources(&source, &[("identity.c", c_source)])
                .expect_err("an invalid source operation must not be rescued by the true goal");
            assert!(error.message().contains(diagnostic), "{body}: {error:?}");
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn grouped_outcome_fold_is_local_to_the_returning_branch() {
    let c_source = r#"
        int32 select(int32* cell, int32 flag) {
            if (flag != 0) { cell[0] = 7; return 7; }
            return 0;
        }
    "#;
    let click_source = r#"
        resource seven_cell(cell: int32*) { owns cell[0..1]; fact cell[0] == 7; }
        verifying "select.c";
        int32 select(int32* cell, int32 flag) {
            owns seven_cell(cell);
            ensures result == 0 or result == 7;
        } by {
            if (flag != 0) {
                unfold(seven_cell(cell));
                step_until(function.exit);
                have cell[0] == 7 by { close(); }
                fold(seven_cell(cell));
                close();
            } else {
                step_until(function.exit);
                close();
            }
        }
    "#;
    let sources = &[("select.c", c_source)];
    let verified_for_expansion = verify_c_sources(click_source, sources)
        .expect("each branch closes its own scalar and resource claims");
    let expanded =
        expand_checked_grouped_claim(click_source, &verified_for_expansion, "select").unwrap();
    verify_c_sources(&expanded, sources)
        .expect("branch-local fold expansion independently verifies");
    let wrong_result = expanded.replace("result == 0 or result == 7", "result == 7");
    assert_ne!(wrong_result, expanded);
    verify_c_sources(&wrong_result, sources)
        .expect_err("the zero-returning sibling cannot borrow the seven-result completion");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_11")]
fn aggregate_return_claims_retain_checked_completions() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/struct_aggregate_return_postcondition.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, body)| (name.as_str(), body.as_str()))
        .collect::<Vec<_>>();
    let verified = verify_c_sources(source, &sources).unwrap();
    assert_eq!(verified.len(), 4);
    assert!(
        verified
            .iter()
            .all(|claim| claim.checked_proposition.is_some())
    );
    let expanded = expand_c_claim_source(
        source,
        &sources,
        "clone_packet",
        ContractProofClaim::Grouped,
    )
    .unwrap();
    verify_c_sources(&expanded, &sources).unwrap();
    let tampered = expanded.replace(
        "ensures result.tag == source->tag;",
        "ensures result.tag == source->inner.flag;",
    );
    assert_ne!(tampered, expanded);
    assert!(verify_c_sources(&tampered, &sources).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_11")]
fn sorry_without_the_flag_is_rejected_at_parse() {
    let c_source = "int32 f(int32 x) { return x + 1; }";
    let click_source = r#"
        verifying "t.c";
        int32 f(int32 x) {
            ensures result == x + 1;
        } by {
            sorry();
        }
    "#;
    let _ = crate::surface::verification::take_sorry_admissions();
    let error = verify_c_sources(click_source, &[("t.c", c_source)])
        .expect_err("sorry without --allow-sorry must fail");
    assert!(
        error.message().contains("--allow-sorry"),
        "unexpected sorry rejection: {}",
        error.message()
    );
    assert!(crate::surface::verification::take_sorry_admissions().is_empty());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_11")]
fn sorry_admits_a_grouped_contract_under_the_flag_without_counting_it_verified() {
    let c_source = "int32 f(int32 x) { return x + 1; }";
    let click_source = r#"
        verifying "t.c";
        int32 f(int32 x) {
            ensures result == x + 1;
        } by {
            sorry();
        }
    "#;
    let _ = crate::surface::verification::take_sorry_admissions();
    let verified = crate::surface::verification::with_allow_sorry(|| {
        verify_c_sources(click_source, &[("t.c", c_source)])
    })
    .expect("sorry under --allow-sorry must admit the contract");
    assert!(
        verified.is_empty(),
        "an admitted contract must not produce verified theorems"
    );
    let admissions = crate::surface::verification::take_sorry_admissions();
    assert_eq!(admissions.len(), 1);
    assert_eq!(admissions[0].label, "f.contract");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_12")]
fn bare_mid_script_sorry_is_rejected_to_keep_holes_minimal() {
    let c_source = "int32 f(int32 x) { int32 y = x; return y; }";
    let click_source = r#"
        verifying "t.c";
        int32 f(int32 x) {
            ensures result == x;
        } by {
            step();
            sorry();
        }
    "#;
    let _ = crate::surface::verification::take_sorry_admissions();
    let error = crate::surface::verification::with_allow_sorry(|| {
        verify_c_sources(click_source, &[("t.c", c_source)])
    })
    .expect_err("bare mid-script sorry must fail: it would cover an unbounded suffix");
    assert!(
        error.message().contains("sorry"),
        "unexpected rejection: {}",
        error.message()
    );
    assert!(crate::surface::verification::take_sorry_admissions().is_empty());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_12")]
fn have_sorry_admits_one_fact_while_the_rest_checks() {
    let c_source = "int32 f(int32 x) { return x; }";
    let click_source = r#"
        verifying "t.c";
        int32 f(int32 x) {
            ensures result == x;
        } by {
            step_until(function.exit);
            have result == x by { sorry(); }
            close();
        }
    "#;
    let _ = crate::surface::verification::take_sorry_admissions();
    let verified = crate::surface::verification::with_allow_sorry(|| {
        verify_c_sources(click_source, &[("t.c", c_source)])
    })
    .expect("have-sorry must admit the fact and check the rest");
    assert!(
        !verified.is_empty(),
        "the contract still yields theorems around the admission"
    );
    let admissions = crate::surface::verification::take_sorry_admissions();
    assert_eq!(admissions.len(), 1);
    assert!(
        admissions[0].label.contains("have result == x"),
        "unexpected admission label: {}",
        admissions[0].label
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3.5s in the parallel gate"]
fn nested_loop_retains_inferred_unchanged_counter_invariants() {
    let c = r#"uint64 nested(uint64 total) {
 uint64 remaining = total;
 while (remaining >= 16UL) {
  remaining -= 16UL;
  uint32 n = 2U;
  while (n > 0U) { n -= 1U; }
 }
 return remaining;
}
"#;
    let proof = r#"verifying "nested.c";
uint64 nested(uint64 total) {
 requires total <= 64u64;
 ensures result < 16u64;
} by {
 step_until(loop(0).entry);
 loop {
  decreases to_integer(remaining);
  invariant remaining <= total;
  invariant total <= 64u64;
  initialize by close();
  maintain by {
   have 16u64 <= remaining by close();
   have to_integer(remaining - 16u64) == to_integer(remaining) - 16;
   mark before_subtract;
   step(); step_until(loop(1).entry);
   loop {
    decreases to_integer(n);
    invariant n <= 2u32;
    invariant remaining <= total - 16u64;
    invariant 16u64 <= total;
    invariant total <= 64u64;
    initialize by {
     have remaining <= total - 16u64 by close() using {
      at(before_subtract, remaining) <= total;
      16u64 <= at(before_subtract, remaining); total <= 64u64;
      remaining == at(before_subtract, remaining) - 16u64;
     };
     have 16u64 <= total by close() using { 16u64 <= at(before_subtract, remaining); at(before_subtract, remaining) <= total; };
     close();
    }
    maintain by {
     have remaining <= total - 16u64 by close();
     have 1u32 <= n by close() using { n > 0u32; n <= 2u32; };
     have to_integer(n - 1u32) == to_integer(n) - 1;
     mark before_inner;
     step();
     have to_integer(n) == at(before_inner, to_integer(n)) - 1 by close() using {
      n == at(before_inner, n) - 1u32;
      at(before_inner, to_integer(n - 1u32)) == at(before_inner, to_integer(n)) - 1;
     };
     have to_integer(n) <= 2 by close() using {
      to_integer(n) == at(before_inner, to_integer(n)) - 1;
      at(before_inner, to_integer(n)) <= 2;
     };
     have 0 <= to_integer(n);
     have to_integer(n) < at(before_inner, to_integer(n)) by close() using {
      to_integer(n) == at(before_inner, to_integer(n)) - 1;
     };
    }
   }
   have remaining <= total by close() using { remaining <= total - 16u64; 16u64 <= total; total <= 64u64; };
   have to_integer(remaining) == at(before_subtract, to_integer(remaining)) - 16 by close() using {
    remaining == at(before_subtract, remaining) - 16u64;
    at(before_subtract, to_integer(remaining - 16u64)) == at(before_subtract, to_integer(remaining)) - 16;
   };
   have 0 <= to_integer(remaining);
   have to_integer(remaining) < at(before_subtract, to_integer(remaining)) by close() using {
    to_integer(remaining) == at(before_subtract, to_integer(remaining)) - 16;
   };
   close();
  }
 }
 step_until(function.exit); close();
}
"#;
    verify_c_sources(proof, &[("nested.c", c)]).unwrap();
    let expanded = expand_c_claim_source(
        proof,
        &[("nested.c", c)],
        "nested",
        ContractProofClaim::Ensure(0),
    )
    .unwrap();
    verify_c_sources(&expanded, &[("nested.c", c)]).unwrap();
    for invalid in [
        proof.replace(
            "invariant remaining <= total - 16u64;",
            "invariant remaining <= total - 17u64;",
        ),
        proof.replace("ensures result < 16u64;", "ensures result < 15u64;"),
    ] {
        assert_ne!(proof, invalid);
        assert!(verify_c_sources(&invalid, &[("nested.c", c)]).is_err());
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_12")]
fn a_function_cannot_assume_its_own_pointer_return_type_guarantee() {
    let c = [(
        "return.c",
        "struct node { unsigned long long word; }; struct node* get(void* p) { return (struct node*)p; }",
    )];
    let source = r#"verifying "return.c";
        function node_type(p: struct node*) -> int32 { 1 }
        struct node* get(void* p) { POST }
    "#;
    verify_c_sources(
        &source.replace("POST", "ensures address(result) == address(p);"),
        &c,
    )
    .unwrap();
    assert!(
        verify_c_sources(
            &source.replace(
                "POST",
                "ensures result != 0 implies node_type(result) == 1;"
            ),
            &c
        )
        .is_err()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_12")]
fn casts_of_resource_fields_keep_their_declared_scalar_types() {
    let c = "void preserve(int32* p) {}";
    let source = r#"
        verifying "field.c";
        abstract resource obj(p: int32*) { field size: int32; }
        void preserve(int32* p) {
            owns o: obj(p);
            requires o.size == -1;
            ensures (o.size as int64) == -1i64;
        } by {
            have (o.size as int32) == o.size by normalize();
            step_until(function.exit); close();
        }
    "#;
    verify_c_sources(source, &[("field.c", c)])
        .expect("casts must see the resource field's declared machine type");
    let unknown = source.replace("(o.size as int32)", "(o.missing as int32)");
    let refusal = verify_c_sources(&unknown, &[("field.c", c)])
        .expect_err("a cast cannot hide a missing resource field");
    assert!(
        refusal.message().contains("has no field `missing`"),
        "{refusal:?}"
    );
    let mathematical = source.replace("field size: int32", "field size: Integer");
    verify_c_sources(&mathematical, &[("field.c", c)])
        .expect_err("a C cast cannot replace an explicit Integer conversion");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_13")]
fn contract_claims_cannot_hide_overflow_behind_reflexivity() {
    let c = "int32 identity(int32 x) { return x; }";
    // Specification `/` and `%` are total at a zero divisor, so only signed
    // `MIN / -1` remains partial.
    for expression in ["result / 0", "result % 0"] {
        let source = format!(
            r#"verifying "domain.c";
            int32 identity(int32 x) {{
                ensures to_integer({expression}) == to_integer({expression});
            }} by {{ step(); close(); }}
        "#
        );
        verify_c_sources(&source, &[("domain.c", c)])
            .unwrap_or_else(|error| panic!("{expression} is total: {error:?}"));
    }
    for expression in [
        "result + 1",
        "result / -1",
        "result % -1",
        "to_uint8(to_integer(result))",
    ] {
        let source = format!(
            r#"verifying "domain.c";
            int32 identity(int32 x) {{
                ensures to_integer({expression}) == to_integer({expression});
            }} by {{ step(); close(); }}
        "#
        );
        assert!(
            verify_c_sources(&source, &[("domain.c", c)]).is_err(),
            "{expression} must have a domain"
        );
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_13")]
fn contract_quantifier_domains_keep_the_chosen_witness_and_polarity() {
    let c = "int32 identity(int32 x) { return x; }";
    for (claim, proof, passes) in [
        (
            "exists (k: int32) { to_integer(k + 1) == 0 }",
            "witness(-1); close();",
            true,
        ),
        (
            "forall (k: int32) { to_integer(k + 1) == to_integer(k + 1) }",
            "intro(); normalize();",
            false,
        ),
        (
            "not (exists (k: int32) { to_integer(k + 1) != to_integer(k + 1) })",
            "intro(); normalize();",
            false,
        ),
        (
            "not (forall (k: int32) { to_integer(k + 1) != 0 })",
            "witness(-1); close();",
            true,
        ),
        (
            "not (forall (k: int32) { to_integer(k + 1) != to_integer(k + 1) })",
            "witness(2147483647); close();",
            false,
        ),
    ] {
        let source = format!(
            r#"verifying "domain.c";
            int32 identity(int32 x) {{ ensures {claim} by {{ step(); {proof} }} }}
        "#
        );
        let result = verify_c_sources(&source, &[("domain.c", c)]);
        assert_eq!(result.is_ok(), passes, "{claim}: {result:?}");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_13")]
fn contract_logical_read_facts_do_not_grant_access() {
    let c = "int32 identity(int32* p) { return 0; }";
    let source = r#"verifying "domain.c";
        int32 identity(int32* p) { ensures p[0] == p[0]; }
    "#;
    verify_c_sources(source, &[("domain.c", c)]).expect("logical reflexivity is total");
    let source = source.replace("p[0] == p[0]", "defined(p[0])");
    verify_c_sources(&source, &[("domain.c", c)])
        .expect_err("logical read naming grants no access");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_13")]
fn opaque_contract_predicate_proof_still_owes_its_body_domain() {
    let c = "int32 identity(int32 x) { return x; }";
    let source = r#"verifying "domain.c";
        predicate reflexive(x: int32) { to_integer(x + 1) == to_integer(x + 1) }
        int32 identity(int32 x) { ensures reflexive(result); }
    "#;
    verify_c_sources(source, &[("domain.c", c)])
        .expect_err("an opaque predicate cannot conceal overflow");
    let bounded = source.replace(
        "ensures reflexive",
        "requires x < 2147483647; ensures reflexive",
    );
    verify_c_sources(&bounded, &[("domain.c", c)])
        .expect("the predicate is defined under the required bound");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_14")]
fn exceptional_contract_claims_discharge_their_own_domains() {
    let c = "int32 helper(int32 x) { return x; } int32 caller(int32 x) { return helper(x); }";
    for (exception, claim, passes) in [
        ("7", "to_integer(exception + 1) == 8", true),
        (
            "2147483647",
            "to_integer(exception + 1) == to_integer(exception + 1)",
            false,
        ),
        (
            "7",
            "to_integer(exception / 0) == to_integer(exception / 0)",
            true,
        ),
        (
            "-2147483648",
            "to_integer(exception / -1) == to_integer(exception / -1)",
            false,
        ),
    ] {
        let source = format!(
            r#"verifying "domain.c";
            int32 helper(int32 x) throws int32 {{
                ensures result == x;
                exceptional ensures exception == {exception};
            }}
            int32 caller(int32 x) throws int32 {{
                ensures result == x;
                exceptional ensures {claim};
            }}
        "#
        );
        let result = verify_c_sources(&source, &[("domain.c", c)]);
        assert_eq!(result.is_ok(), passes, "{claim}: {result:?}");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_14")]
fn contract_arithmetic_domain_refusal_retains_the_actual_goal_and_checked_context() {
    let source = r#"verifying "claim_domain.c";
        int32 identity(int32 x) {
            ensures to_integer(result + 1) == to_integer(result + 1);
        }
    "#;
    let error = verify_c_sources(
        source,
        &[("claim_domain.c", "int32 identity(int32 x) { return x; }")],
    )
    .expect_err("the claim still owes its signed addition domain");
    assert!(error.to_string().contains("unclosed goal:"), "{error}");
    let requirement = error
        .unresolved_requirement()
        .expect("claim wrappers retain the actual debt");
    assert!(requirement.context.is_some());
    assert!(
        error.diagnostic().is_some(),
        "checked scope must survive the wrapper"
    );
    let report = error.report();
    assert!(report.contains("goal:"), "{report}");
    assert!(report.contains("evaluation requirement"), "{report}");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by contract_batch_14")]
fn contract_domain_refusal_retains_the_actual_goal_and_checked_context() {
    let source = r#"verifying "claim_domain.c";
        int32 identity(int32 x) {
            ensures to_uint8(to_integer(result)) == to_uint8(to_integer(result));
        }
    "#;
    let error = verify_c_sources(
        source,
        &[("claim_domain.c", "int32 identity(int32 x) { return x; }")],
    )
    .expect_err("the claim still owes its integer conversion domain");
    assert!(error.to_string().contains("unclosed goal:"), "{error}");
    let requirement = error
        .unresolved_requirement()
        .expect("claim wrappers retain the actual debt");
    // Conversion bounds have no optional producer description. Their actual
    // proposition and the checked diagnostic scope must still survive.
    assert!(matches!(
        requirement.proposition,
        Proposition::ConditionIs(_, true)
    ));
    assert!(
        error.diagnostic().is_some(),
        "checked scope must survive the wrapper"
    );
    let report = error.report();
    assert!(report.contains("goal:"), "{report}");
    assert!(report.contains("evaluation requirement"), "{report}");
}

#[cfg(feature = "fast-gate")]
test_batches! {
    file: "contract_tests.rs",
    marker: "contract_batch_",
    contract_batch_00: [
        inline_array_element_addresses_are_logical_without_granting_access,
        historical_wide_view_bound_reads_the_marked_counter,
        unsigned_word_array_field_contracts_decay_to_typed_addresses,
        modular_exceptional_call_continues_through_a_normal_assignment,
    ],
    contract_batch_01: [
        successive_modular_exceptional_calls_keep_each_throw_path,
        exceptional_call_before_a_normal_branch_retains_its_exit,
        exceptional_call_before_two_returning_normal_arms_retains_its_exit,
        nonterminal_exceptional_call_rejects_a_false_caller_claim,
    ],
    contract_batch_02: [
        nonterminal_call_cannot_drop_an_unconstrained_exception,
        modular_exceptional_call_completes_both_caller_claim_families,
        modular_exceptional_call_rejects_a_false_caller_claim,
        targeted_exceptional_caller_assumes_but_does_not_certify_an_unselected_callee,
    ],
    contract_batch_03: [
        exceptional_contracts_publish_distinct_claim_families,
        exceptional_contract_bindings_are_family_specific,
        abstract_resource_construction_adds_one_authorized_token,
        abstract_resource_construction_requires_function_authorization,
        closing_constructs_only_a_missing_authorized_output_token,
    ],
    contract_batch_04: [
        contradiction_closes_an_impossible_concrete_outcome,
        flat_function_proof_stays_on_proof_through_claim_acceptance,
        individual_linear_open_proof_stays_on_proof_through_claim_acceptance,
        proof_if_splits_one_frontier_after_execution_has_started,
    ],
    contract_batch_05: [
        post_execution_resource_fold_completes_without_a_body_rerun,
        implicitly_closed_population_entry_completes_without_a_body_rerun,
        callee_subrange_requirement_completes_without_a_body_rerun,
        token_quantity_entry_completes_without_a_body_rerun,
    ],
    contract_batch_06: [
        grouped_flat_function_proof_stays_on_one_proof_through_claim_acceptance,
        grouped_n_way_function_outcomes_stay_on_one_proof,
        grouped_n_way_outcomes_discard_exactly_infeasible_siblings_on_proof,
        grouped_calls_keep_contract_transitions_on_proof,
    ],
    contract_batch_07: [
        grouped_opaque_calls_keep_declared_composite_resources_on_proof,
        grouped_sequential_top_level_scopes_stay_on_one_proof,
        grouped_predicate_contracts_stay_on_one_proof,
        heap_backed_predicate_contract_stays_on_checked_proof,
    ],
    contract_batch_08: [
        quantified_heap_scope_stays_on_checked_proof,
        grouped_leading_resource_relations_stay_on_one_proof,
        grouped_owned_outcome_resources_stay_on_one_proof,
        flat_function_expansion_rewrites_and_rejects_tampering,
    ],
    contract_batch_09: [
        post_execution_frame_using_relowers_a_preceding_have_fact,
        ordinary_verification_stops_at_the_tactic_work_budget,
        verifies_omitted_proof_with_default_prover,
        solve_rejects_loop_backed_claims,
    ],
    contract_batch_10: [
        verifies_memory_postcondition,
        verifies_quantified_old_memory_postcondition,
        owned_segment_rejects_write_outside_owned_memory,
        sequence_contracts_reject_mixed_and_non_equality_types,
    ],
    contract_batch_11: [
        source_have_failures_keep_the_written_operation_in_each_execution_phase,
        aggregate_return_claims_retain_checked_completions,
        sorry_without_the_flag_is_rejected_at_parse,
        sorry_admits_a_grouped_contract_under_the_flag_without_counting_it_verified,
    ],
    contract_batch_12: [
        bare_mid_script_sorry_is_rejected_to_keep_holes_minimal,
        have_sorry_admits_one_fact_while_the_rest_checks,
        a_function_cannot_assume_its_own_pointer_return_type_guarantee,
        casts_of_resource_fields_keep_their_declared_scalar_types,
    ],
    contract_batch_13: [
        contract_claims_cannot_hide_overflow_behind_reflexivity,
        contract_quantifier_domains_keep_the_chosen_witness_and_polarity,
        contract_logical_read_facts_do_not_grant_access,
        opaque_contract_predicate_proof_still_owes_its_body_domain,
    ],
    contract_batch_14: [
        exceptional_contract_claims_discharge_their_own_domains,
        contract_arithmetic_domain_refusal_retains_the_actual_goal_and_checked_context,
        contract_domain_refusal_retains_the_actual_goal_and_checked_context,
    ],
}

#[test]
fn contract_closing_preserves_proposition_identity_through_explicit_proofs() {
    let source = "struct packet { uint32 n; }; void change(uint32* n) { *n = 9; } uint32 consume(struct packet p) { uint32 before = p.n; change(&p.n); return before; }";
    let proof = r#"verifying "closing.c";
        void change(uint32* n) { owns n[0..1]; ensures *n == 9u32; }
        uint32 consume(struct packet p) { ensures result == old(p.n); }
    "#;
    let inputs = [("closing.c", source)];
    let (verified, events) = crate::instrumentation::collect(|| verify_c_sources(proof, &inputs));
    let verified = verified.unwrap();
    assert_eq!(verified.len(), 3);
    assert_eq!(
        verified
            .iter()
            .filter(|theorem| theorem.checked_proposition.is_some())
            .count(),
        2
    );
    assert!(!events.iter().any(|event| matches!(event,
        crate::instrumentation::VerificationEvent::OperationFinished { name, .. } if name == "ensure lowering"
    )), "completed postconditions must not be lowered again");
    let expanded = expand_checked_grouped_claim(proof, &verified, "consume").unwrap();
    verify_c_sources(&expanded, &inputs).unwrap();
    let wrong = proof.replace("ensures result == old(p.n);", "ensures result == 9u32;");
    let error = verify_c_sources(&wrong, &inputs).unwrap_err();
    assert!(
        !error.message().contains("could not certify contract"),
        "{error}"
    );
}

#[test]
fn contract_closing_keeps_state_clauses_as_local_obligations() {
    let source = "int unchanged(int x) { return x; }";
    let proof = r#"verifying "closing.c";
        int32 unchanged(int32 x) {
            ensures result == at(region(0).entry, x);
        } by { step(); normalize(); }
    "#;
    let inputs = [("closing.c", source)];
    verify_c_sources(proof, &inputs).unwrap();
    let wrong = proof.replace(
        "result == at(region(0).entry, x)",
        "result != at(region(0).entry, x)",
    );
    assert!(verify_c_sources(&wrong, &inputs).is_err());
}

#[test]
fn contract_closing_retains_resource_and_write_footprint_completions() {
    let inputs = [(
        "closing.c",
        "int counter; int write(void) { counter = 9; return 0; }",
    )];
    let proof = r#"verifying "closing.c";
        int32 write() { owns counter; ensures result == 0; }
    "#;
    let (verified, events) = crate::instrumentation::collect(|| verify_c_sources(proof, &inputs));
    let verified = verified.unwrap();
    assert!(!events.iter().any(|event| matches!(event,
        crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
            if name == "storage write footprint check" || name == "implicit empty effect check" || name == "contract path preparation"
    )));
    let expanded = expand_checked_grouped_claim(proof, &verified, "write").unwrap();
    without_implicit_solve(|| verify_c_sources(&expanded, &inputs)).unwrap();

    let missing_ownership = proof.replace("owns counter;", "");
    let (result, events) =
        crate::instrumentation::collect(|| verify_c_sources(&missing_ownership, &inputs));
    assert!(
        result
            .unwrap_err()
            .message()
            .contains("outside the mutable footprint")
    );
    assert!(
        !events.iter().any(|event| matches!(
            event,
            crate::instrumentation::VerificationEvent::ContractClaimsFinished { .. }
        )),
        "an unproved footprint is refused before contract registration"
    );
}
