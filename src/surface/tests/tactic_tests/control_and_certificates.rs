use super::*;

fn check_nonzero_after_integer_rewrites(ty: &str, suffix: &str) {
    let source = format!(
        r#"import click::integer;
theorem carried_nonzero(u: int64, v: {ty}, z: Integer) {{
 requires to_integer(u) == z;
 requires z == to_integer(v);
 requires v != 0{suffix};
 ensures u != 0i64 by {{
  rewrite(to_integer(u), z);
  rewrite(z, to_integer(v));
  close();
 }}
}}"#
    );
    verify_click_theorems(&source).expect("native nonzero closes the rewritten Integer goal");
    let missing_fact = source.replace(&format!(" requires v != 0{suffix};\n"), "");
    assert!(verify_click_theorems(&missing_fact).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_00")]
fn known_closes_rewritten_native_int32_nonzero() {
    check_nonzero_after_integer_rewrites("int32", "");
}
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_00")]
fn known_closes_rewritten_native_uint32_nonzero() {
    check_nonzero_after_integer_rewrites("uint32", "u32");
}
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_00")]
fn known_closes_rewritten_native_int64_nonzero() {
    check_nonzero_after_integer_rewrites("int64", "i64");
}
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_00")]
fn known_closes_rewritten_native_uint64_nonzero() {
    check_nonzero_after_integer_rewrites("uint64", "u64");
}

fn check_integer_rewrite_of_nested_native_bounds(ty: &str, suffix: &str) {
    let source = format!(
        r#"import click::integer;
    theorem observed_bounds(x: {ty}, y: Integer) {{
        requires to_integer(x) == y;
        requires y <= 10;
        requires y <= 20;
        ensures x <= 10{suffix} and x <= 20{suffix} by {{
            rewrite(to_integer(x), y);
            all {{ y <= 10 => {{ close(); }} y <= 20 => {{ close(); }} }}
        }}
    }}"#
    );
    verify_click_theorems(&source).expect("the rewrite reaches both native comparison leaves");
    let false_bound = source.replace(
        &format!("ensures x <= 10{suffix}"),
        &format!("ensures x <= 9{suffix}"),
    );
    assert!(verify_click_theorems(&false_bound).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_01")]
fn integer_rewrite_reaches_nested_native_int32_bounds() {
    check_integer_rewrite_of_nested_native_bounds("int32", "");
}
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_01")]
fn integer_rewrite_reaches_nested_native_uint32_bounds() {
    check_integer_rewrite_of_nested_native_bounds("uint32", "u32");
}
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_01")]
fn integer_rewrite_reaches_nested_native_int64_bounds() {
    check_integer_rewrite_of_nested_native_bounds("int64", "i64");
}
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_01")]
fn integer_rewrite_reaches_nested_native_uint64_bounds() {
    check_integer_rewrite_of_nested_native_bounds("uint64", "u64");
}

fn rewritten_integer_division_goal_source(quotient: bool) -> String {
    let source = r#"import click::integer;
function prefix(n: Integer) -> Integer { n - truncating_remainder(n, 4) }
theorem prefix_bound(n: uint64) {
 requires n <= 22207u64;
 requires to_integer(n - n % 4u64) <= 22204;
 requires to_integer(n - n % 4u64) == to_integer(n) - truncating_remainder(to_integer(n), 4);
 requires 0 <= prefix(to_integer(n));
 requires prefix(to_integer(n)) <= 22204;
 ensures 0 <= to_integer(n - n % 4u64) and to_integer(n - n % 4u64) <= 22204 by {
  rewrite(to_integer(n - n % 4u64), to_integer(n) - truncating_remainder(to_integer(n), 4));
  unfold(prefix(to_integer(n)));
  all {
      0 <= to_integer(n) - truncating_remainder(to_integer(n), 4) => {
       close() using { 0 <= prefix(to_integer(n)); prefix(to_integer(n)) == to_integer(n) - truncating_remainder(to_integer(n), 4); };
      }
      to_integer(n) - truncating_remainder(to_integer(n), 4) <= 22204 => {
       close();
      }
  }
 }
}
"#;
    if quotient {
        source
            .replace(
                "n - truncating_remainder(n, 4)",
                "truncating_quotient(n, 4) * 4",
            )
            .replace("n - n % 4u64", "n / 4u64 * 4u64")
            .replace(
                "to_integer(n) - truncating_remainder(to_integer(n), 4)",
                "truncating_quotient(to_integer(n), 4) * 4",
            )
    } else {
        source.to_owned()
    }
}

fn check_rewritten_integer_division_goal(quotient: bool) {
    let source = rewritten_integer_division_goal_source(quotient);
    let verified = verify_click_theorems(&source)
        .expect("arithmetic retains a spelling after rewrite and both");
    let prefix = source.split_once(" by {").unwrap().0;
    let expanded = format!(
        "{prefix} {}\n}}",
        verified[0].expanded_proof_source().unwrap()
    );
    assert!(!expanded.contains("close() using"), "{expanded}");
    verify_click_theorems(&expanded).expect("the explicit proof verifies independently");
    let false_bound = source.replacen("ensures 0 <=", "ensures 1 <=", 1);
    assert_ne!(source, false_bound);
    assert!(verify_click_theorems(&false_bound).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_02")]
fn rewritten_remainder_goals_synthesize_through_both() {
    check_rewritten_integer_division_goal(false);
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_02")]
fn rewritten_quotient_goals_synthesize_through_both() {
    check_rewritten_integer_division_goal(true);
}

const CONDITIONAL_QUOTIENT_C: &str = "int identity(int x, int d) { return x; }";
const CONDITIONAL_QUOTIENT_CLAIM: &str = r#"import click::integer;
verifying "identity.c";
int32 identity(int32 x, int32 d) {
    requires d > 0;
    ensures x < 0 implies truncating_quotient(to_integer(result), to_integer(d)) == truncating_quotient(to_integer(x), to_integer(d));
} by { step_until(function.exit); intro(); close(); }
"#;

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_02")]
fn conditional_quotient_claim_reuses_its_checked_domain() {
    let sources = [("identity.c", CONDITIONAL_QUOTIENT_C)];
    verify_c_sources(CONDITIONAL_QUOTIENT_CLAIM, &sources)
        .expect("the completed conditional claim includes its guarded divisor obligation");
    let false_claim = CONDITIONAL_QUOTIENT_CLAIM.replace(
        "truncating_quotient(to_integer(x), to_integer(d));",
        "truncating_quotient(to_integer(x), to_integer(d)) + 1;",
    );
    assert!(verify_c_sources(&false_claim, &sources).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_02")]
fn conditional_quotient_claim_keeps_its_domain_in_expansion() {
    let sources = [("identity.c", CONDITIONAL_QUOTIENT_C)];
    let position = expansion::position_at_offset(
        CONDITIONAL_QUOTIENT_CLAIM,
        CONDITIONAL_QUOTIENT_CLAIM.find("close()").unwrap(),
    );
    let expanded = expand_c_tactic_source_at(
        CONDITIONAL_QUOTIENT_CLAIM,
        &sources,
        position.line,
        position.column,
    )
    .expect("the completed quotient claim expands");
    assert!(!expanded.contains("solve()"), "{expanded}");
    verify_c_sources(&expanded, &sources).expect("the explicit claim verifies independently");
    let missing_domain = CONDITIONAL_QUOTIENT_CLAIM.replace("requires d > 0;", "");
    assert!(verify_c_sources(&missing_domain, &sources).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_03")]
fn integer_certificate_keeps_negative_observation_bounds_when_adding() {
    let source = r#"theorem zero_add_bound(q: int64) {
 requires -9223372036854775808 <= to_integer(q);
 requires to_integer(q) <= 9223372036854775807;
 ensures -9223372036854775808 <= to_integer(q + 0i64) by {
  have defined(q + 0i64) by close();
  have to_integer(q + 0i64) == to_integer(q) + 0;
  close() using {
   to_integer(q + 0i64) == to_integer(q) + 0;
   -9223372036854775808 <= to_integer(q);
   to_integer(q) <= 9223372036854775807;
  };
 }
}
"#;
    verify_c_sources(source, &[]).expect("the native zero-add equality transports the lower bound");
    let position = expansion::position_at_offset(source, source.find("close() using").unwrap());
    let expanded = expand_c_tactic_source_at(source, &[], position.line, position.column)
        .expect("the arithmetic proof expands");
    assert!(!expanded.contains("close() using"), "{expanded}");
    verify_c_sources(&expanded, &[])
        .expect("the explicit certificate preserves the negative bound");
    let false_claim = source.replace(
        "ensures -9223372036854775808 <=",
        "ensures -9223372036854775807 <=",
    );
    assert!(verify_c_sources(&false_claim, &[]).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_03")]
fn both_and_proves_exact_conjuncts_and_rejects_incomplete_arms() {
    let source = r#"
        theorem pair(x: int32) {
            ensures x == x and (x <= x and x >= x) by {
                all {
                    x == x => { normalize(); }
                    (x <= x and x >= x) => {
                        all { x <= x => { normalize(); } x >= x => { normalize(); } }
                    }
                }
            }
        }
    "#;
    let verify_explicit = |source: &str| {
        crate::surface::proof::without_implicit_solve(|| verify_c_sources(source, &[]))
    };
    verify_explicit(source).expect("nested exact conjunction proofs");
    for bad in [
        source.replacen("x == x => { normalize(); }", "x == x => { }", 1),
        source.replace("x >= x", "x > x"),
        source.replacen("x >= x => { normalize(); }", "", 1),
        source.replacen("x == x =>", "x <= x =>", 1),
        source.replace(
            "all { x <= x => { normalize(); } x >= x => { normalize(); } }",
            "all { normalize(); } and { normalize(); }",
        ),
    ] {
        assert!(verify_explicit(&bad).is_err(), "{bad}");
    }
    let leaking = r#"theorem leak(x: int32) {
        ensures (x == 0 implies x == 0) and x == 0 by {
            all { (x == 0 implies x == 0) => { intro(); close(); } x == 0 => { close(); } }
        }
    }"#;
    assert!(
        verify_c_sources(leaking, &[]).is_err(),
        "left assumptions must not leak to the right"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_03")]
fn both_and_outcome_expands_and_rechecks() {
    let c = "int32 identity(int32 x) { return x; }";
    let source = r#"verifying "identity.c";
        int32 identity(int32 x) { ensures result == x and result <= x; } by {
            step(); all { result == x => { close(); } result <= x => { close(); } }
        }
    "#;
    let sources = [("identity.c", c)];
    let verified_for_expansion = verify_c_sources(source, &sources).expect("both at an outcome");
    let expanded =
        expand_checked_grouped_claim(source, &verified_for_expansion, "identity").unwrap();
    assert!(expanded.contains("all {"), "{expanded}");
    assert!(
        expanded.find("result == x => {").unwrap() < expanded.find("result <= x => {").unwrap(),
        "{expanded}"
    );
    verify_c_sources(&expanded, &sources).expect("expanded child proofs");
    let position = expansion::position_at_offset(source, source.find("close();").unwrap());
    let selected =
        expand_c_tactic_source_at(source, &sources, position.line, position.column).unwrap();
    verify_c_sources(&selected, &sources).expect("selected both expansion");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_04")]
fn parses_frontier_branch_tactic() {
    let source = FILL3_CLICK.replace(
        "== 2;",
        "== 2 by { branch { true => { step(); } false => { step_until(function.exit); } } }",
    );
    let file = parse(&source).expect("frontier branch tactic should parse");
    let tactics = file.function_blocks()[0].ensures()[0]
        .proof()
        .tactics()
        .expect("expected tactics");

    assert!(matches!(
        &tactics[0],
        ProofTactic::Branch(ProofBranch {
            ensuring: None,
            then_tactics,
            else_tactics,
        }) if then_tactics == &[ProofTactic::Step]
            && else_tactics == &[ProofTactic::ExecuteUntil(ExecutionPoint::FUNCTION_EXIT)]
    ));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_04")]
fn parses_frontier_branch_ensuring_interface() {
    let source = FILL3_CLICK.replace("== 2;", "== 2 by { branch ensuring { fact i >= 0; owns p[0..3]; } { true => { step(); } false => { step_until(function.exit); } } }",
    );
    let file = parse(&source).expect("frontier branch ensuring interface should parse");
    let tactics = file.function_blocks()[0].ensures()[0]
        .proof()
        .tactics()
        .expect("expected tactics");

    assert!(matches!(
        &tactics[0],
        ProofTactic::Branch(ProofBranch {
            ensuring: Some(assertions),
            then_tactics,
            else_tactics,
        }) if matches!(assertions.as_slice(), [
            ProofAssertion::Fact(_),
            ProofAssertion::Resource(ResourceClause::OwnMemory(_)),
        ]) && then_tactics == &[ProofTactic::Step]
            && else_tactics == &[ProofTactic::ExecuteUntil(ExecutionPoint::FUNCTION_EXIT)]
    ));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_04")]
fn linear_frontier_branch_uses_the_checked_structural_join() {
    let c_source = r#"
        int32 constant(int32 x) {
            if (x < 0) {
                x = 1;
            } else {
                x = 1;
            }
            return x;
        }
    "#;
    let click_source = r#"
        verifying "constant.c";

        predicate selected(x: int32) { x == x }

        int32 constant(int32 x) {
            requires selected(x);
            ensures returns_one: result == 1;
        } by {
            branch {
                true => {
                    unfold(selected(x));
                    step();
                }
                false => {
                    unfold(selected(x));
                    step();
                }
            }
            step();
            close();
        }
    "#;

    verify_c_sources(click_source, &[("constant.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "linear frontier branch should retain and check its arm proofs: {}",
            error.message()
        )
    });

    let captured = super::super::proof::capture_program_tactic_expansion(
        click_source,
        &[("constant.c", c_source)],
        super::super::expansion::ProofSite::FunctionClaim {
            function_name: "constant".to_string(),
            claim: ContractProofClaim::Grouped,
        },
        0,
        &[],
    );
    let captured = captured.expect("the checked branch should expose its retained expansion");
    assert!(
        matches!(
            captured.as_slice(),
            [ProofTactic::Branch(branch)]
                if branch.ensuring.is_none()
                    && branch.then_tactics.len() == 2
                    && branch.else_tactics.len() == 2
        ),
        "{captured:#?}"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_04")]
fn terminal_frontier_branch_seals_without_a_body_rerun() {
    let c_source = r#"
        int32 choose_sign(int32 x) {
            if (x < 0) {
                return 1;
            } else {
                return 2;
            }
        }
    "#;
    let click_source = r#"
        verifying "choose_sign.c";

        int32 choose_sign(int32 x) {
            ensures result == 1 or result == 2;
        } by {
            branch { true => { step(); } false => { step(); } }
            close();
        }
    "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c_sources(click_source, &[("choose_sign.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "terminal C branch should retain its checked path evidence: {}",
            error.message()
        )
    });
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "terminal C branch proof and opaque certification should reuse the retained path evidence"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_05")]
fn successive_shared_continuation_branches_seal_without_path_multiplication() {
    let c_source = r#"
        int32 two_branches(int32 x, int32 y) {
            if (x < 0) {
            } else {
            }
            if (y < 0) {
            } else {
            }
            return x;
        }
    "#;
    let click_source = r#"
        verifying "two_branches.c";

        int32 two_branches(int32 x, int32 y) {
            ensures result == x;
        } by {
            branch { true => {} false => {} }
            branch { true => {} false => {} }
            step();
            close();
        }
    "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    verify_c_sources(click_source, &[("two_branches.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "successive shared-continuation branches should retain a nested evidence node apiece: {}",
            error.message()
        )
    });
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "successive joins should seal one continuation rather than flattening all path combinations"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_05")]
fn decided_frontier_branch_retains_the_only_feasible_checked_arm() {
    let c_source = r#"
        int32 constant_negative(int32 x) {
            if (x < 0) {
                x = 1;
            } else {
                x = 2;
            }
            return x;
        }
    "#;
    let click_source = r#"
        verifying "constant_negative.c";

        int32 constant_negative(int32 x) {
            requires x < 0;
            ensures returns_one: result == 1 by {
                branch { true => { step(); } false => { step(); } }
                step();
                close();
            }
        }
    "#;

    let (verified, flat_units) = proof::count_flat_proof_units(|| {
        verify_c_sources(click_source, &[("constant_negative.c", c_source)])
    });
    let verified = verified.expect("the decided C branch should retain its checked path");
    assert_eq!(flat_units, 1, "the decided proof should retain one Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the decided branch should retain an expansion");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::If(proof_if))
                if proof_if.then_tactics.len() == 2 && proof_if.else_tactics.is_empty()
        ),
        "the feasible then path should be retained with its structural entry step: {tactics:#?}"
    );

    let captured = super::super::proof::capture_program_tactic_expansion(
        click_source,
        &[("constant_negative.c", c_source)],
        super::super::expansion::ProofSite::FunctionClaim {
            function_name: "constant_negative".to_string(),
            claim: ContractProofClaim::Ensure(0),
        },
        0,
        &[],
    );
    let captured = captured.expect("the decided source branch should expose its expansion");
    assert!(
        matches!(
            captured.as_slice(),
            [ProofTactic::If(proof_if)]
                if proof_if.then_tactics.len() == 2 && proof_if.else_tactics.is_empty()
        ),
        "the selected source branch should expose the checked decided path: {captured:#?}"
    );

    let expanded = expand_c_claim_source(
        click_source,
        &[("constant_negative.c", c_source)],
        "constant_negative",
        ContractProofClaim::Ensure(0),
    );
    let expanded = expanded.expect("the decided branch should expand");
    verify_c_sources(&expanded, &[("constant_negative.c", c_source)])
        .expect("the serialized decided proof should independently reverify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_05")]
fn rejects_removed_reach_tactic() {
    let source = FILL3_CLICK.replace(
        "== 2;",
        "== 2 by { reach(region(1).exit) ensuring { fact i >= 0; } by { step(); } }",
    );
    let error = parse(&source).expect_err("removed reach tactic should not parse");

    assert!(error.message().contains("unknown tactic `reach`"));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_05")]
fn empty_proof_if_branches_contribute_only_their_case_split() {
    // Owner decision 2026-07-31: an empty `if` branch is legal in a proof
    // script — it contributes its case split and every path goal stays owed
    // at path end. Pure case-split certificates expand to exactly this shape.
    let c_source = r#"
            int32 sign_bit(int32 x) {
                if (x < 0) {
                    return 1;
                }
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "sign.c";

            int32 sign_bit(int32 x) {
                ensures result == 0 or result == 1;
            } by {
                if x < 0 {
                } else {
                }
            }
        "#;
    verify_c_sources(click_source, &[("sign.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "empty proof-if branches should parse and verify: {}",
            error.message()
        )
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_06")]
fn parses_execute_until_proof_tactic() {
    let source = FILL3_CLICK.replace(
        "== 2;",
        "== 2 by { step_until(region(1).entry); step_until(function.exit); close(); }",
    );
    let file = parse(&source).expect("execute_until explicit proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some(
            [
                ProofTactic::ExecuteUntil(ExecutionPoint::ProgramPoint(ProgramPointRef {
                    region: CodeRegionRef::Region(1),
                    kind: ProgramPointKind::Entry
                })),
                ProofTactic::ExecuteUntil(ExecutionPoint::FUNCTION_EXIT),
                ProofTactic::Close,
            ]
            .as_slice()
        )
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_06")]
fn parses_unfold_proof_tactic() {
    let source = FILL3_CLICK.replace(
        "== 2;",
        "== 2 by { step_until(function.exit); unfold(sorted(p, 2)); close(); }",
    );
    let file = parse(&source).expect("unfold explicit proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some(
            [
                ProofTactic::ExecuteUntil(ExecutionPoint::FUNCTION_EXIT),
                ProofTactic::UnfoldFunction(ClickFunctionApplication {
                    name: "sorted".into(),
                    arguments: vec![
                        ContractExpression::ProgramExpression(ProgramExpression::Variable(
                            "p".into()
                        )),
                        ContractExpression::IntegerLiteral("2".into())
                    ]
                }),
                ProofTactic::Close,
            ]
            .as_slice()
        )
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_06")]
fn parses_apply_theorem_proof_tactic() {
    let source = FILL3_CLICK.replace(
        "== 2;",
        "== 2 by { step_until(function.exit); apply(nonnegative(result)); close(); }",
    );
    let file = parse(&source).expect("apply explicit proof script should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert_eq!(
        ensure.proof().tactics(),
        Some(
            [
                ProofTactic::ExecuteUntil(ExecutionPoint::FUNCTION_EXIT),
                ProofTactic::ApplyTheorem(TheoremApplication {
                    name: "nonnegative".to_string(),
                    arguments: vec![current_var("result")],
                }),
                ProofTactic::Close,
            ]
            .as_slice()
        )
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_06")]
fn rejects_apply_theorem_with_explicit_premises() {
    let source = FILL3_CLICK.replace(
        "== 2;",
        "== 2 by {
            step_until(function.exit);
            apply(nonnegative(result)) using { 0 <= result; };
            close();
        }",
    );
    let error = parse(&source).expect_err("named theorem application uses the facts in scope");
    assert!(
        error
            .message()
            .contains("application takes no `using` list")
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_07")]
fn parses_transport_with_explicit_premises() {
    let source = FILL3_CLICK.replace(
        "== 2;",
        "== 2 by {
            step();
            transport(old(p[0]) == 0, p[0] == 0) using {
                old(p[0]) == 0;
            }
            step_until(function.exit);
            close();
        }",
    );
    let file = parse(&source).expect("explicit-premise transport should parse");
    let ensure = &file.function_blocks()[0].ensures()[0];

    assert!(matches!(
        &ensure.proof().tactics().expect("expected tactics")[1],
        ProofTactic::TransportUsing { premises, .. } if premises.len() == 1
    ));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_07")]
fn parses_and_classifies_simple_and_smart_tactics() {
    let source = r#"
            theorem rewritten(x: int32, y: int32) {
                requires x == y;
                ensures x == y by {
                    rewrite(x, y);
                    normalize();
                }
            }
        "#;
    let file = parse(source).expect("simple tactics should parse");
    let tactics = file.theorem_definitions()[0].ensures()[0]
        .proof()
        .tactics()
        .expect("expected tactics");

    assert!(matches!(
        tactics[0].class(),
        TacticClass::Simple(SimpleTactic::Rewrite)
    ));
    assert!(matches!(
        tactics[1].class(),
        TacticClass::Simple(SimpleTactic::Normalize)
    ));
    assert!(matches!(
        ProofTactic::Solve.class(),
        TacticClass::Smart(SmartSite::Engine(SmartTacticKind::Solve))
    ));
    assert!(matches!(
        ProofTactic::SolveUsing(ProofSolveUsing {
            premises: Vec::new(),
        })
        .class(),
        TacticClass::Smart(SmartSite::Engine(SmartTacticKind::Solve))
    ));
    assert!(matches!(
        ProofTactic::Step.class(),
        TacticClass::Simple(SimpleTactic::StatementTransition)
    ));
    let application = TheoremApplication {
        name: "rewritten".to_string(),
        arguments: vec![current_int(0), current_int(0)],
    };
    assert!(matches!(
        ProofTactic::ApplyTheorem(application.clone()).class(),
        TacticClass::Simple(SimpleTactic::ApplyTheorem)
    ));
    assert!(matches!(
        ProofTactic::ApplyTheoremUsing {
            application,
            premises: vec![ClickProposition::Defined {
                expression: current_int(0),
            }],
        }
        .class(),
        TacticClass::Simple(SimpleTactic::ApplyTheorem)
    ));
    let transport_source = ClickProposition::Defined {
        expression: current_int(0),
    };
    let transport_target = ClickProposition::Defined {
        expression: current_int(1),
    };
    assert!(matches!(
        ProofTactic::Transport {
            source: transport_source.clone(),
            target: transport_target.clone(),
        }
        .class(),
        TacticClass::Smart(SmartSite::Elided(ElidedArgument::FrameEvidence))
    ));
    assert!(matches!(
        ProofTactic::TransportUsing {
            source: transport_source,
            target: transport_target,
            premises: Vec::new(),
        }
        .class(),
        TacticClass::Simple(SimpleTactic::FactTransport)
    ));
    assert!(matches!(
        ProofTactic::Step.class(),
        TacticClass::Simple(SimpleTactic::StatementTransition)
    ));
    assert!(matches!(
        ProofTactic::Step.class(),
        TacticClass::Simple(SimpleTactic::StatementTransition)
    ));
    assert!(matches!(
        ProofTactic::FoldResource(ResourceClause::Declared {
            type_schema: None,
            resource_type_arguments: Vec::new(),
            resource_arguments: Vec::new(),
            access: ResourceAccessMode::Own,
            kind: ResourceKind::Composite,
            name: "cell".to_string(),
            arguments: vec![],
            parameter_types: vec![],
        })
        .class(),
        TacticClass::Simple(SimpleTactic::FoldResource)
    ));
    assert!(matches!(
        ProofTactic::CloseInvariants.class(),
        TacticClass::Smart(SmartSite::CloseInvariants)
    ));
    assert!(matches!(
        ProofTactic::Mark("before_write".to_string()).class(),
        TacticClass::Simple(SimpleTactic::Mark)
    ));
    assert!(matches!(
        ProofTactic::Step.class(),
        TacticClass::Simple(SimpleTactic::StatementTransition)
    ));
    assert!(matches!(
        ProofTactic::Step.class(),
        TacticClass::Simple(SimpleTactic::StatementTransition)
    ));
    assert!(matches!(
        ProofTactic::SmartExecute.class(),
        TacticClass::Smart(SmartSite::Engine(SmartTacticKind::Execute))
    ));
    assert!(matches!(
        ProofTactic::ExecuteUntil(ExecutionPoint::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Region(1),
            kind: ProgramPointKind::Entry
        }))
        .class(),
        TacticClass::Smart(SmartSite::Engine(SmartTacticKind::Execute))
    ));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_07")]
fn canonical_tactic_printer_round_trips_nested_surface_certificate() {
    let nonnegative = ClickProposition::Comparison {
        left: ContractExpression::ProgramExpression(ProgramExpression::Variable(
            ("x".to_string()).into(),
        )),
        operator: ComparisonOperator::GreaterEqual,
        right: ContractExpression::IntegerLiteral("0".into()),
    };
    let tactics = vec![
        ProofTactic::Mark("before_step".to_string()),
        ProofTactic::Step,
        ProofTactic::If(ProofIf {
            ensuring: None,
            condition: nonnegative.clone(),
            then_tactics: vec![ProofTactic::Have(ProofHave {
                proposition: nonnegative.clone(),
                proof: SourceProof::Script(vec![ProofTactic::Known]),
            })],
            else_tactics: vec![ProofTactic::Normalize],
        }),
    ];
    let certificate = ProofCertificate::from_proof_tactics(&tactics)
        .expect("test tactics should form a surface certificate");
    let printed = format_proof_certificate(&certificate);
    let source = format!(
        r#"
            verifying "printer.c";

            int32 printer(int32 x) {{
                ensures x == x;
            }} {printed}
        "#
    );
    let parsed = parse(&source).expect("printed certificate should parse");
    assert_eq!(
        crate::surface::printing::format_partial_tactic_sequence(
            parsed.function_blocks()[0]
                .grouped_proof()
                .unwrap()
                .tactics()
                .unwrap()
        ),
        crate::surface::printing::format_partial_tactic_sequence(&tactics)
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_07")]
fn canonical_tactic_printer_round_trips_cases_certificate() {
    let nonnegative = ClickProposition::Comparison {
        left: ContractExpression::ProgramExpression(ProgramExpression::Variable(
            ("x".to_string()).into(),
        )),
        operator: ComparisonOperator::GreaterEqual,
        right: ContractExpression::IntegerLiteral("0".into()),
    };
    let negative = ClickProposition::Comparison {
        left: ContractExpression::ProgramExpression(ProgramExpression::Variable(
            ("x".to_string()).into(),
        )),
        operator: ComparisonOperator::LessThan,
        right: ContractExpression::IntegerLiteral("0".into()),
    };
    let disjunction =
        ClickProposition::Or(Box::new(nonnegative.clone()), Box::new(negative.clone()));
    let tactics = vec![
        ProofTactic::Have(ProofHave {
            proposition: disjunction.clone(),
            proof: SourceProof::Script(vec![ProofTactic::Cases(ProofCases::new(vec![
                ProofCaseArm::new(nonnegative.clone(), vec![ProofTactic::Known]),
                ProofCaseArm::new(negative.clone(), vec![ProofTactic::Known]),
            ]))]),
        }),
        ProofTactic::Enumerate,
    ];
    let certificate = ProofCertificate::from_proof_tactics(&tactics)
        .expect("a cases script should form a surface certificate");
    let printed = format_proof_certificate(&certificate);
    let source = format!(
        r#"
            verifying "printer.c";

            int32 printer(int32 x) {{
                ensures x == x;
            }} {printed}
        "#
    );
    let parsed = parse(&source).expect("printed cases certificate should parse");
    assert_eq!(
        crate::surface::printing::format_partial_tactic_sequence(
            parsed.function_blocks()[0]
                .grouped_proof()
                .unwrap()
                .tactics()
                .unwrap()
        ),
        crate::surface::printing::format_partial_tactic_sequence(&tactics)
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_08")]
fn proof_certificate_round_trips_nested_surface_steps() {
    let reflexive = ClickProposition::Comparison {
        left: current_var("x"),
        operator: ComparisonOperator::Equal,
        right: current_var("x"),
    };
    let tactics = vec![
        ProofTactic::Mark("entry".to_string()),
        ProofTactic::Have(ProofHave {
            proposition: reflexive.clone(),
            proof: SourceProof::Script(vec![ProofTactic::Normalize]),
        }),
        ProofTactic::Branch(ProofBranch {
            ensuring: Some(vec![ProofAssertion::Fact(reflexive)]),
            then_tactics: vec![ProofTactic::Known],
            else_tactics: vec![ProofTactic::Normalize],
        }),
    ];

    let proof = ProofCertificate::from_proof_tactics(&tactics)
        .expect("surface tactics should construct a simple proof");

    assert_eq!(proof.to_proof_tactics(), tactics);
    assert!(matches!(
        proof.steps(),
        [
            ProofStep::Mark(_),
            ProofStep::Have { .. },
            ProofStep::Branch { .. }
        ]
    ));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_08")]
fn proof_certificate_has_no_smart_step_variant() {
    let smart = ProofCertificate::from_proof_tactics(&[ProofTactic::Solve])
        .expect_err("smart tactics cannot appear in a proof certificate");
    assert_eq!(
        smart.tactic_class(),
        TacticClass::Smart(SmartSite::Engine(SmartTacticKind::Solve))
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_08")]
fn tactic_certificate_accepts_only_simple_tactics() {
    let tactics = vec![
        ProofTactic::Rewrite(ClickProposition::Comparison {
            left: current_var("x"),
            operator: ComparisonOperator::Equal,
            right: current_var("y"),
        }),
        ProofTactic::Normalize,
    ];

    let certificate =
        ProofCertificate::from_proof_tactics(&tactics).expect("simple tactics form a certificate");

    assert_eq!(certificate.to_proof_tactics(), tactics);
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_08")]
fn tactic_certificate_rejects_a_direct_smart_tactic() {
    let error = ProofCertificate::from_proof_tactics(&[ProofTactic::Solve])
        .expect_err("a smart tactic cannot be a certificate leaf");

    assert_eq!(
        error.tactic_class(),
        TacticClass::Smart(SmartSite::Engine(SmartTacticKind::Solve))
    );
    assert_eq!(error.path(), &[CertificatePathSegment::Tactic(0)]);
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_09")]
fn tactic_certificate_rejects_smart_tactics_in_nested_control_tactics() {
    let condition = ClickProposition::Comparison {
        left: current_var("x"),
        operator: ComparisonOperator::Equal,
        right: current_var("x"),
    };
    let tactics = [ProofTactic::Branch(ProofBranch {
        ensuring: None,
        then_tactics: vec![ProofTactic::If(ProofIf {
            ensuring: None,
            condition,
            then_tactics: vec![ProofTactic::Have(ProofHave {
                proposition: ClickProposition::Comparison {
                    left: current_var("x"),
                    operator: ComparisonOperator::Equal,
                    right: current_var("x"),
                },
                proof: SourceProof::Script(vec![ProofTactic::Solve]),
            })],
            else_tactics: vec![ProofTactic::Normalize],
        })],
        else_tactics: vec![ProofTactic::Normalize],
    })];

    let error = ProofCertificate::from_proof_tactics(&tactics)
        .expect_err("nested smart tactics cannot be hidden in a certificate");

    assert_eq!(
        error.tactic_class(),
        TacticClass::Smart(SmartSite::Engine(SmartTacticKind::Solve))
    );
    assert_eq!(
        error.path(),
        &[
            CertificatePathSegment::Tactic(0),
            CertificatePathSegment::ThenBranch,
            CertificatePathSegment::Tactic(0),
            CertificatePathSegment::ThenBranch,
            CertificatePathSegment::Tactic(0),
            CertificatePathSegment::HaveBody,
            CertificatePathSegment::Tactic(0),
        ]
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_09")]
fn tactic_certificate_checks_structural_induction_arms() {
    let tactics = [
        ProofTactic::Induct {
            parameter: "xs".into(),
            hypothesis: "ih".into(),
        },
        ProofTactic::Match(std::sync::Arc::new(ProofMatch {
            scrutinee: ContractExpression::Binding("xs".into()),
            ensuring: None,
            arms: vec![ProofInductionArm {
                type_name: "List".into(),
                variant: "Nil".into(),
                bindings: Vec::new(),
                tactics: vec![ProofTactic::Solve],
            }],
        })),
    ];

    let error = ProofCertificate::from_proof_tactics(&tactics)
        .expect_err("smart tactics cannot be hidden in an induction arm");
    assert_eq!(
        error.tactic_class(),
        TacticClass::Smart(SmartSite::Engine(SmartTacticKind::Solve))
    );
    assert_eq!(
        error.path(),
        &[
            CertificatePathSegment::Tactic(1),
            CertificatePathSegment::MatchArm(0),
            CertificatePathSegment::Tactic(0),
        ]
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_09")]
fn tactic_certificate_treats_an_omitted_nested_proof_as_solve() {
    let tactics = [ProofTactic::Have(ProofHave {
        proposition: ClickProposition::Comparison {
            left: current_var("x"),
            operator: ComparisonOperator::Equal,
            right: current_var("x"),
        },
        proof: SourceProof::Default,
    })];

    let error = ProofCertificate::from_proof_tactics(&tactics)
        .expect_err("an omitted nested proof is smart solve");

    assert_eq!(
        error.tactic_class(),
        TacticClass::Smart(SmartSite::Implicit)
    );
    assert_eq!(
        error.path(),
        &[
            CertificatePathSegment::Tactic(0),
            CertificatePathSegment::HaveBody,
        ]
    );
}

/// `close_invariants()` plans the back-edge bundle body, so it is smart and
/// no certificate can hold it. The retained step is `close_invariants() by`,
/// which carries that planned body explicitly.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_09")]
fn tactic_certificate_rejects_a_bare_invariant_closure() {
    let error = ProofCertificate::from_proof_tactics(&[ProofTactic::CloseInvariants])
        .expect_err("a bare invariant closure cannot be a certificate leaf");

    assert_eq!(
        error.tactic_class(),
        TacticClass::Smart(SmartSite::CloseInvariants)
    );
    assert_eq!(error.path(), &[CertificatePathSegment::Tactic(0)]);
}

/// Serialized evidence is admitted by the same rule as source text: a
/// structural `loop` step whose phase was never planned is a smart proof, and
/// `from_steps` refuses it exactly as `from_proof_tactics` refuses an omitted
/// `maintain by`.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_10")]
fn step_certificate_rejects_a_loop_step_with_an_unplanned_phase() {
    let complete = CertificateStructuralClause {
        region: CodeRegion::Loop(0),
        label: None,
        decreases: None,
        diverges: false,
        items: Vec::new(),
        resources: Vec::new(),
        initialize_proof: Some(Box::new(
            ProofCertificate::from_steps(vec![ProofStep::Normalize])
                .expect("a simple step is a certificate"),
        )),
        otherwise_proof: None,
        preserve_proof: Some(Box::new(
            ProofCertificate::from_steps(vec![ProofStep::Known])
                .expect("a simple step is a certificate"),
        )),
    };
    ProofCertificate::from_steps(vec![ProofStep::Loop(complete.clone())])
        .expect("a loop step with both phases planned is a certificate");

    let mut unplanned = complete;
    unplanned.preserve_proof = None;
    let error = ProofCertificate::from_steps(vec![ProofStep::Loop(unplanned)])
        .expect_err("an unplanned preservation phase is not a certificate");
    let message = error.message().to_string();
    assert!(message.contains("loop `maintain`"), "{message}");
    assert!(message.contains("the implicit closer"), "{message}");
}

const ORDERED_PAIR_C: &str = r#"
    struct pair {
        int32 low;
        int32 high;
    };

    void set_pair(struct pair* pair, int32 bound) {
        pair->low = 0;
        pair->high = bound;
    }
"#;

const ORDERED_PAIR_CLICK: &str = r#"
    predicate ordered_pair(pair: struct pair*) {
        0 <= pair->low and pair->low <= pair->high
    }

    verifying "set_pair.c";

    void set_pair(struct pair* pair, int32 bound) {
        requires 0 <= bound;
        owns *pair;

        ensures ordered_pair(pair);
    } by {
        step_until(function.exit);
        have ordered_pair(pair) by {
            unfold(ordered_pair(pair));
            close();
        }
        close();
    }
"#;

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_10")]
fn smart_have_splits_an_unfolded_predicate_conjunction_goal() {
    // The `have`'s smart `solve` closes a predicate body that unfolds to a
    // conjunction of scalar bounds. The constructed certificate must split
    // the conjunction into per-conjunct `have` certificates; before the
    // split, the whole-conjunction goal had no explicit simple certificate.
    verify_c_sources(ORDERED_PAIR_CLICK, &[("set_pair.c", ORDERED_PAIR_C)]).unwrap_or_else(
        |error| {
            panic!(
                "the unfolded conjunction goal should split per conjunct: {}",
                error.message()
            )
        },
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_10")]
fn fixed_state_have_certifies_a_post_call_fact_across_a_later_store() {
    // After the call to `reset`, the fact `pair->low == 0` is recorded
    // against the call's post-state state; the later store to
    // `pair->high` moves the current memory past it. The mid-proof `have`
    // must still produce a checking certificate for the fact in its
    // current form. (The full stale-form rewrite rejection is
    // exercised by `examples/bounded-pool`'s `pool_pipeline`.)
    let reset_source = r#"
        struct pair {
            int32 low;
            int32 high;
        };

        void reset(struct pair* pair) {
            pair->low = 0;
        }
    "#;
    let touch_source = r#"
        struct pair {
            int32 low;
            int32 high;
        };

        void touch(struct pair* pair) {
            reset(pair);
            pair->high = 5;
        }
    "#;
    let click_source = r#"
        verifying "reset.c";
        verifying "touch.c";

        void reset(struct pair* pair) {
            owns *pair;

            ensures pair->low == 0;
        }

        void touch(struct pair* pair) {
            owns *pair;

            ensures pair->low == 0;
        } by {
            step();
            step();
            have pair->low == 0 by close();
            step();
            close();
        }
    "#;

    verify_c_sources(
        click_source,
        &[("reset.c", reset_source), ("touch.c", touch_source)],
    )
    .unwrap_or_else(|error| {
        panic!(
            "the post-call have should certify without a stale-form rewrite: {}",
            error.message()
        )
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_10")]
fn grouped_outcome_solve_splits_an_unfold_active_conjunction_ensure() {
    // The final `solve` certifies `ordered_pair(pair)` while `unfold` is
    // active, so the kernel goal is already the body conjunction while the
    // surface goal is the predicate call. The certificate must unfold the
    // surface goal in step and split the conjunction.
    let c_source = r#"
        struct pair {
            int32 low;
            int32 high;
        };

        void bump(struct pair* pair) {
            pair->low = pair->low + 1;
        }
    "#;
    let click_source = r#"
        predicate ordered_pair(pair: struct pair*) {
            0 <= pair->low and pair->low <= pair->high
        }

        verifying "bump.c";

        void bump(struct pair* pair) {
            requires ordered_pair(pair);
            requires pair->low < pair->high;
            owns *pair;

            ensures ordered_pair(pair);
        } by {
            unfold(ordered_pair(pair));
            step_until(function.exit);
            close();
        }
    "#;

    verify_c_sources(click_source, &[("bump.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "the unfold-active conjunction ensure should split per conjunct: {}",
            error.message()
        )
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_11")]
fn parses_execute_until_assignment_and_preserves_same_spelled_labels() {
    for (spelling, region) in [
        (
            "assignment(i, 2)",
            CodeRegionRef::Assignment {
                local: "i".into(),
                occurrence: 2,
            },
        ),
        ("assignment", CodeRegionRef::Label("assignment".into())),
    ] {
        let source = FILL3_CLICK.replace(
            "== 2;",
            &format!(
                "== 2 by {{ step_until({spelling}.entry); step_until(function.exit); close(); }}"
            ),
        );
        let file = parse(&source).unwrap();
        assert_eq!(
            file.function_blocks()[0].ensures()[0]
                .proof()
                .tactics()
                .unwrap()[0],
            ProofTactic::ExecuteUntil(ExecutionPoint::ProgramPoint(ProgramPointRef {
                region,
                kind: ProgramPointKind::Entry
            }))
        );
    }
    for spelling in ["assignment(i, -1)", "assignment(i)", "assignment(, 0)"] {
        let source = FILL3_CLICK.replace(
            "== 2;",
            &format!("== 2 by {{ step_until({spelling}.entry); }}"),
        );
        assert!(parse(&source).is_err());
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by control_batch_11")]
fn parses_execute_until_read_and_preserves_read_labels() {
    for (spelling, region) in [
        ("read(2)", CodeRegionRef::Read(2)),
        ("read", CodeRegionRef::Label("read".into())),
    ] {
        let source = FILL3_CLICK.replace(
            "== 2;",
            &format!(
                "== 2 by {{step_until({spelling}.entry); step_until(function.exit); close();}}"
            ),
        );
        let file = parse(&source).unwrap();
        assert_eq!(
            file.function_blocks()[0].ensures()[0]
                .proof()
                .tactics()
                .unwrap()[0],
            ProofTactic::ExecuteUntil(ExecutionPoint::ProgramPoint(ProgramPointRef {
                region,
                kind: ProgramPointKind::Entry
            }))
        );
    }
}

#[cfg(feature = "fast-gate")]
test_batches! {
    file: "control_and_certificates.rs",
    marker: "control_batch_",
    control_batch_00: [
        known_closes_rewritten_native_int32_nonzero,
        known_closes_rewritten_native_uint32_nonzero,
        known_closes_rewritten_native_int64_nonzero,
        known_closes_rewritten_native_uint64_nonzero,
    ],
    control_batch_01: [
        integer_rewrite_reaches_nested_native_int32_bounds,
        integer_rewrite_reaches_nested_native_uint32_bounds,
        integer_rewrite_reaches_nested_native_int64_bounds,
        integer_rewrite_reaches_nested_native_uint64_bounds,
    ],
    control_batch_02: [
        rewritten_remainder_goals_synthesize_through_both,
        rewritten_quotient_goals_synthesize_through_both,
        conditional_quotient_claim_reuses_its_checked_domain,
        conditional_quotient_claim_keeps_its_domain_in_expansion,
    ],
    control_batch_03: [
        integer_certificate_keeps_negative_observation_bounds_when_adding,
        both_and_proves_exact_conjuncts_and_rejects_incomplete_arms,
        both_and_outcome_expands_and_rechecks,
    ],
    control_batch_04: [
        parses_frontier_branch_tactic,
        parses_frontier_branch_ensuring_interface,
        linear_frontier_branch_uses_the_checked_structural_join,
        terminal_frontier_branch_seals_without_a_body_rerun,
    ],
    control_batch_05: [
        successive_shared_continuation_branches_seal_without_path_multiplication,
        decided_frontier_branch_retains_the_only_feasible_checked_arm,
        rejects_removed_reach_tactic,
        empty_proof_if_branches_contribute_only_their_case_split,
    ],
    control_batch_06: [
        parses_execute_until_proof_tactic,
        parses_unfold_proof_tactic,
        parses_apply_theorem_proof_tactic,
        rejects_apply_theorem_with_explicit_premises,
    ],
    control_batch_07: [
        parses_transport_with_explicit_premises,
        parses_and_classifies_simple_and_smart_tactics,
        canonical_tactic_printer_round_trips_nested_surface_certificate,
        canonical_tactic_printer_round_trips_cases_certificate,
    ],
    control_batch_08: [
        proof_certificate_round_trips_nested_surface_steps,
        proof_certificate_has_no_smart_step_variant,
        tactic_certificate_accepts_only_simple_tactics,
        tactic_certificate_rejects_a_direct_smart_tactic,
    ],
    control_batch_09: [
        tactic_certificate_rejects_smart_tactics_in_nested_control_tactics,
        tactic_certificate_checks_structural_induction_arms,
        tactic_certificate_treats_an_omitted_nested_proof_as_solve,
        tactic_certificate_rejects_a_bare_invariant_closure,
    ],
    control_batch_10: [
        step_certificate_rejects_a_loop_step_with_an_unplanned_phase,
        smart_have_splits_an_unfolded_predicate_conjunction_goal,
        fixed_state_have_certifies_a_post_call_fact_across_a_later_store,
        grouped_outcome_solve_splits_an_unfold_active_conjunction_ensure,
    ],
    control_batch_11: [
        parses_execute_until_assignment_and_preserves_same_spelled_labels,
        parses_execute_until_read_and_preserves_read_labels,
    ],
}

#[test]
fn named_conjunct_proofs_match_labels_in_either_order() {
    let source = r#"
        theorem conjunction(x: int32) {
            ensures (x == x and x <= x) and x == x by {
                all {
                    x <= x => { normalize(); }
                    x == x => { normalize(); }
                    x == x => { normalize(); }
                }
            }
        }
    "#;
    verify_click_theorems(source).unwrap();
    assert!(verify_click_theorems(&source.replace("all {", "all positional {")).is_err());

    let grouped = r#"
        theorem grouped() {
            ensures (forall (i: int32) { i == i }) and (2 == 2 and 3 == 3) by {
                all {
                    (2 == 2 and 3 == 3) => {
                        all { 3 == 3 => { normalize(); } 2 == 2 => { normalize(); } }
                    }
                    forall (j: int32) { j == j } => { intro(); normalize(); }
                }
            }
        }
    "#;
    let expanded = expand_c_claim_source_by_label(grouped, &[], "grouped.ensures_0").unwrap();
    crate::surface::proof::without_implicit_solve(|| verify_click_theorems(&expanded)).unwrap();
    for (changed, reason) in [
        (
            source.replace("x <= x => { normalize(); }", ""),
            "is missing an arm for this conjunct",
        ),
        (
            source.replace("x <= x => { normalize(); }", "x < x => { normalize(); }"),
            "is missing an arm for this conjunct",
        ),
        (
            source.replace(
                "x <= x => { normalize(); }",
                "x <= x => { normalize(); } x <= x => { normalize(); }",
            ),
            "has no corresponding conjunct",
        ),
        (source.replace("all {", "both {"), "`both` is retired"),
    ] {
        let error = verify_click_theorems(&changed).unwrap_err().report();
        assert!(error.contains(reason), "{error}");
    }
}
