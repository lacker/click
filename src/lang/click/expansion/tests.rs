use super::*;

#[test]
fn block_tactic_optional_semicolon_belongs_to_the_tactic() {
    let source = "by { step() using {}; simp(); }";
    let tokens = scan_source_tokens(source).expect("source should tokenize");
    let by = tokens
        .iter()
        .position(|token| token.text == "by")
        .expect("proof should contain by");
    let open = by + 1;
    let close = matching_delimiter(&tokens, open, "{", "}")
        .expect("proof block should have a closing brace");
    let ranges = direct_tactic_token_ranges(&tokens, open, close)
        .expect("block tactics should be indexable");

    assert_eq!(ranges.len(), 2, "{ranges:?}");
    assert_eq!(tokens[ranges[0].end - 1].text, ";");
    assert_eq!(tokens[ranges[1].end - 1].text, ";");
}

fn expand_top_level_tactic_for_test(
    click_source: &str,
    c_sources: &[(&str, &str)],
    function_name: &str,
    claim: CProofClaim,
    tactic_index: usize,
) -> Result<String, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
    let function = find_function(&tokens, function_name)?;
    let proof = match claim {
        CProofClaim::Grouped => find_grouped_proof_span(&tokens, &function)?,
        CProofClaim::Ensure(_) | CProofClaim::Effect(_) => {
            find_claim_proof_span(&tokens, &function, claim)?
        }
    };
    let span = find_tactic_span(&tokens, &proof, tactic_index)?;
    let position = position_at_offset(click_source, span.start);
    expand_c0_tactic_source_at(click_source, c_sources, position.line, position.column)
}

#[test]
fn expands_one_grouped_tactic_without_running_the_suffix() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = r#"
verifying "identity.c";

int32 identity(int32 x) {
    ensures result == x;
} by {
    execute();
    simp();
}
"#;

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Grouped,
        0,
    )
    .expect("the first grouped tactic should expand");

    assert!(!expanded.contains("execute();"));
    assert!(expanded.contains("    step() using {\n    }\n    simp();"));
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the source with one expanded tactic should re-verify");
}

#[test]
fn expands_grouped_immutable_read_with_multiple_claim_successors() {
    let c_source = "int32 read_first(int32 p[1]) { return p[0]; }";
    let click_source = r#"
verifying "read.c";

int32 read_first(int32 p[1]) {
    views p[0..1];
    immutable;
    ensures result == p[0];
} by {
    execute();
    frame();
    simp();
}
"#;

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &[("read.c", c_source)],
        "read_first",
        CProofClaim::Grouped,
        0,
    )
    .expect("the grouped immutable read should have one common expansion");

    assert!(!expanded.contains("execute();"));
    assert!(expanded.contains("step() using {"), "{expanded}");
    verify_c0_sources(&expanded, &[("read.c", c_source)])
        .expect("the expanded immutable read should re-verify every grouped claim");
}

#[test]
fn expands_nested_branch_tactic_by_source_location() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = r#"
verifying "identity.c";

int32 identity(int32 x) {
    ensures result == x;
} by {
    if x == x {
        execute();
        simp();
    } else {
        execute();
        simp();
    }
}
"#;
    let then_offset = click_source
        .find("        execute();")
        .expect("then tactic should exist")
        + 8;
    let position = position_at_offset(click_source, then_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("identity.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the nested then tactic should expand");

    assert_eq!(expanded.matches("execute();").count(), 1);
    assert!(
        expanded.contains("    if x == x {\n        step() using {"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the source with one nested expansion should re-verify");
}

#[test]
fn source_positions_include_tactics_nested_in_open_blocks() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = r#"
resource known(x: int32) {
    fact x == x;
}

verifying "identity.c";

int32 identity(int32 x) {
    owns known(x);
    ensures result == x;
} by {
    open(known(x)) {
        execute();
    }
    simp();
}
"#;
    let sources = [("identity.c", c_source)];

    let nested = c0_tactic_source_position(click_source, &sources, "identity.contract", 1)
        .expect("the tactic inside `open` should have a source position");
    assert_eq!(
        nested,
        SourcePosition {
            line: 13,
            column: 9
        }
    );

    let continuation = c0_tactic_source_position(click_source, &sources, "identity.contract", 2)
        .expect("the tactic after `open` should retain its source position");
    assert_eq!(
        continuation,
        SourcePosition {
            line: 15,
            column: 5
        }
    );
}

#[test]
fn expands_common_step_after_frontier_branch() {
    let c_source = r#"
int32 increment_selected(int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
    } else {
        y = 0;
    }
    y = y + 1;
    return y;
}
"#;
    let click_source = r#"
verifying "increment.c";

int32 increment_selected(int32 x) {
    requires x < 2147483647;
    ensures result > 0 by {
        step();
        branch {
            ensuring {
                fact y >= 0;
                fact y < 2147483647;
            }
            then {
                step();
            }
            else {
                step();
            }
        }
        step();
        step();
        simp();
    }
}
"#;
    let selected_offset = click_source
        .find("        step();\n        step();\n        simp();")
        .expect("common step should exist")
        + 8;
    let position = position_at_offset(click_source, selected_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("increment.c", c_source)],
        position.line,
        position.column,
    )
    .expect("common step should expand");

    verify_c0_sources(&expanded, &[("increment.c", c_source)]).unwrap_or_else(|error| {
        panic!("expanded common step should replay:\n{error:?}\n{expanded}")
    });
}

#[test]
fn expands_deferred_simp_after_frontier_branch() {
    let c_source = r#"
int32 positive_after_branch(int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
    } else {
        y = 0;
    }
    y = y + 1;
    return y;
}
"#;
    let click_source = r#"
verifying "positive.c";

int32 positive_after_branch(int32 x) {
    requires x < 2147483647;
    ensures result > 0 by {
        step();
        branch {
            ensuring {
                fact y >= 0;
                fact y < 2147483647;
            }
            then {
                step();
            }
            else {
                step();
            }
        }
        step();
        step();
        simp();
    }
}
"#;
    let selected_offset = click_source
        .find("        simp();")
        .expect("simp should exist")
        + 8;
    let position = position_at_offset(click_source, selected_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("positive.c", c_source)],
        position.line,
        position.column,
    )
    .expect("deferred simp should expand");

    verify_c0_sources(&expanded, &[("positive.c", c_source)]).unwrap_or_else(|error| {
        panic!("expanded deferred simp should replay:\n{error:?}\n{expanded}")
    });
}

#[test]
fn shares_equal_deferred_expansions_after_frontier_branch() {
    let c_source = r#"
int32 same_after_branch(int32 x, int32 flag) {
    int32 y;
    if (flag != 0) {
        y = x;
    } else {
        y = x;
    }
    return y;
}
"#;
    let click_source = r#"
verifying "same.c";

int32 same_after_branch(int32 x, int32 flag) {
    ensures result == x by {
        step();
        branch {
            then { step(); }
            else { step(); }
        }
        step();
        simp();
    }
}
"#;
    let selected_offset = click_source
        .find("        simp();")
        .expect("simp should exist")
        + 8;
    let position = position_at_offset(click_source, selected_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("same.c", c_source)],
        position.line,
        position.column,
    )
    .expect("equal deferred certificates should expand");

    assert!(!expanded.contains("if at(statement(1).entry"), "{expanded}");
    verify_c0_sources(&expanded, &[("same.c", c_source)]).unwrap_or_else(|error| {
        panic!("shared deferred expansion should replay:\n{error:?}\n{expanded}")
    });
}

#[test]
fn expands_common_deferred_tactic_with_a_returning_branch_arm() {
    let c_source = r#"
int32 clamp_nonnegative(int32 x) {
    if (x < 0) {
        return 0;
    }
    return x;
}
"#;
    let click_source = r#"
verifying "returning.c";

int32 clamp_nonnegative(int32 x) {
    ensures result >= 0 by {
        branch {
            then {
                step();
                simp();
            }
            else {}
        }
        step();
        simp();
    }
}
"#;
    let selected_offset = click_source
        .rfind("        simp();")
        .expect("common simp should exist")
        + 8;
    let position = position_at_offset(click_source, selected_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("returning.c", c_source)],
        position.line,
        position.column,
    )
    .expect("reachable continuation simp should expand");

    verify_c0_sources(&expanded, &[("returning.c", c_source)]).unwrap_or_else(|error| {
        panic!("returning-arm deferred expansion should replay:\n{error:?}\n{expanded}")
    });
}

#[test]
fn expands_deferred_simp_after_nested_frontier_branches() {
    let c_source = r#"
int32 nested_nonnegative(int32 x, int32 flag) {
    int32 y;
    if (flag != 0) {
        if (x >= 0) {
            y = x;
        } else {
            y = 0;
        }
    } else {
        y = 0;
    }
    return y;
}
"#;
    let click_source = r#"
verifying "nested.c";

int32 nested_nonnegative(int32 x, int32 flag) {
    ensures result >= 0 by {
        step();
        branch {
            ensuring {
                fact y >= 0;
            }
            then {
                branch {
                    ensuring {
                        fact y >= 0;
                    }
                    then { step(); }
                    else { step(); }
                }
            }
            else { step(); }
        }
        step();
        simp();
    }
}
"#;
    let selected_offset = click_source
        .find("        simp();")
        .expect("common simp should exist")
        + 8;
    let position = position_at_offset(click_source, selected_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("nested.c", c_source)],
        position.line,
        position.column,
    )
    .expect("nested deferred simp should expand");

    verify_c0_sources(&expanded, &[("nested.c", c_source)]).unwrap_or_else(|error| {
        panic!("nested deferred expansion should replay:\n{error:?}\n{expanded}")
    });
}

#[test]
fn locates_a_block_tactic_as_one_source_statement() {
    let source = "by { have x == x by simp; simp(); }";
    let tokens = scan_source_tokens(source).expect("source should scan");
    let proof = proof_span(&tokens, 0).expect("proof should have a span");

    let first = find_tactic_span(&tokens, &proof, 0).expect("first tactic should exist");
    let second = find_tactic_span(&tokens, &proof, 1).expect("second tactic should exist");

    assert_eq!(&source[first], "have x == x by simp;");
    assert_eq!(&source[second], "simp();");
}

#[test]
fn hides_statement_local_opaque_call_facts_from_surface_premises() {
    let zero_c = "int32 zero() { return 0; }";
    let caller_c = "int32 caller() { int32 value; value = zero(); return value; }";
    let click_source = r#"
verifying "zero.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    execute();
    simp();
}
"#;
    let sources = [("zero.c", zero_c), ("caller.c", caller_c)];

    let expanded =
        expand_top_level_tactic_for_test(click_source, &sources, "caller", CProofClaim::Grouped, 0)
            .expect("opaque call internals should not become surface premises");

    assert_eq!(expanded.matches("execute();").count(), 1);
    verify_c0_sources(&expanded, &sources)
        .expect("the caller with one expanded tactic should re-verify");
}

#[test]
fn opaque_call_expansion_keeps_only_consumed_ambient_conditions() {
    let positive_c = "int32 positive(int32 x) { return x; }";
    let caller_c = "int32 caller(int32 x) { int32 result; result = positive(x); return result; }";
    let click_source = r#"
verifying "positive.c";
verifying "caller.c";

int32 positive(int32 x) {
    requires 0 < x;
    ensures result == x;
} by {
    execute();
    simp();
}

int32 caller(int32 x) {
    requires 0 < x;
    requires x < 100;
    requires x != 37;
    ensures result == x;
} by {
    execute();
    simp();
}
"#;
    let sources = [("positive.c", positive_c), ("caller.c", caller_c)];

    let expanded =
        expand_top_level_tactic_for_test(click_source, &sources, "caller", CProofClaim::Grouped, 0)
            .expect("the call should expand with its consumed precondition");
    let step_using = expanded
        .split("step() using {")
        .skip(1)
        .filter_map(|rest| rest.split_once('}').map(|(block, _)| block))
        .nth(1)
        .expect("the opaque call should be the second statement step");
    assert!(!step_using.is_empty(), "{expanded}");
    assert!(step_using.contains("0 < x;"), "{expanded}");
    assert!(!step_using.contains("x < 100;"), "{expanded}");
    assert!(!step_using.contains("x != 37;"), "{expanded}");
    verify_c0_sources(&expanded, &sources).expect("the precise call premises should replay");
}

#[test]
fn opaque_call_expansion_keeps_memory_condition_safety() {
    let positive_at_c =
        "struct box { int32 value; }; int32 positive_at(struct box* p) { return p->value; }";
    let caller_c = r#"struct box { int32 value; };
int32 caller(struct box* p, int32 x) {
    int32 result;
    result = positive_at(p);
    return result;
}"#;
    let click_source = r#"
verifying "positive_at.c";
verifying "caller.c";

int32 positive_at(struct box* p) {
    views p->value;
    requires 0 < p->value;
    ensures result == p->value;
} by {
    execute();
    simp();
}

int32 caller(struct box* p, int32 x) {
    views p->value;
    requires 0 < p->value;
    requires x < 100;
    ensures result == p->value;
} by {
    execute();
    simp();
}
"#;
    let sources = [("positive_at.c", positive_at_c), ("caller.c", caller_c)];

    let expanded =
        expand_top_level_tactic_for_test(click_source, &sources, "caller", CProofClaim::Grouped, 0)
            .expect("the memory-reading precondition should expand");
    let step_using = expanded
        .split("step() using {")
        .skip(1)
        .filter_map(|rest| rest.split_once('}').map(|(block, _)| block))
        .nth(1)
        .expect("the opaque call should be the second statement step");
    assert!(step_using.contains("0 < p->value;"), "{expanded}");
    assert!(!step_using.contains("x < 100;"), "{expanded}");
    assert!(step_using.contains("loadable("), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the condition and its loadability should replay");
}

#[test]
fn expands_public_opaque_call_results_through_later_call_arguments() {
    let zero_c = "int32 zero() { return 0; }";
    let passthrough_c = "int32 passthrough(int32 x) { return x; }";
    let caller_c = r#"int32 caller() {
    int32 first;
    int32 second;
    first = zero();
    second = passthrough(first);
    return second;
}"#;
    let click_source = r#"
verifying "zero.c";
verifying "passthrough.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 passthrough(int32 x) {
    ensures result == x;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    execute();
    simp();
}
"#;
    let sources = [
        ("zero.c", zero_c),
        ("passthrough.c", passthrough_c),
        ("caller.c", caller_c),
    ];
    let final_simp = click_source
        .rfind("simp();")
        .expect("caller final simp should exist");
    let position = position_at_offset(click_source, final_simp);

    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("public call facts should compose through their receiving locals");

    assert!(expanded.contains("first"), "{expanded}");
    assert!(expanded.contains("second"), "{expanded}");
    assert!(!expanded.contains("call-havoc"), "{expanded}");
    assert!(!expanded.contains("symbolic-pointer"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the expanded public fact chain should independently re-verify");
}

#[test]
fn grouped_simp_distinguishes_c_local_result_from_contract_result() {
    let zero_c = "int32 zero() { return 0; }";
    let caller_c = "int32 caller() { int32 result; result = zero(); return result; }";
    let click_source = r#"
verifying "zero.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    execute();
    simp();
}
"#;
    let sources = [("zero.c", zero_c), ("caller.c", caller_c)];
    let final_simp = click_source
        .rfind("simp();")
        .expect("caller final simp should exist");
    let position = position_at_offset(click_source, final_simp);

    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("the grouped simp should expand across the local result assignment");

    verify_c0_sources(&expanded, &sources)
        .expect("the explicit C result binding should replay without aliasing contract result");

    let explicit_source = r#"
verifying "zero.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    execute();
    have at(statement(2).entry, c(result)) == 0 by {
        assumption();
    }
    have result == at(statement(2).entry, c(result)) by {
        normalize();
    }
    assumption();
}
"#;
    verify_c0_sources(explicit_source, &sources)
        .expect("`c(result)` should denote the C local rather than contract result");
}

#[test]
fn selected_tactic_requires_the_complete_function_dependency_closure() {
    let zero_c = "int32 zero() { return 1; }";
    let caller_c = "int32 caller() { int32 value; value = zero(); return value; }";
    let click_source = r#"
verifying "zero.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    step();
    execute();
    simp();
}
"#;
    let sources = [("zero.c", zero_c), ("caller.c", caller_c)];

    let error =
        expand_top_level_tactic_for_test(click_source, &sources, "caller", CProofClaim::Grouped, 0)
            .expect_err("capture must reject an invalid callee used later in the proof unit");
    assert!(error.message().contains("zero.ensures_0"));
    assert!(
        error
            .message()
            .contains("grouped `simp` could not certify its complete claim transition")
    );
}

#[test]
fn grouped_simp_expansion_preserves_each_claim_closer() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = r#"
verifying "identity.c";

int32 identity(int32 x) {
    ensures result == x;
    ensures result == old(x);
} by {
    execute();
    simp();
}
"#;
    let sources = [("identity.c", c_source)];

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &sources,
        "identity",
        CProofClaim::Grouped,
        1,
    )
    .expect("grouped simp should expand");

    assert_eq!(expanded.matches("assumption();").count(), 2);
    verify_c0_sources(&expanded, &sources)
        .expect("each grouped claim closer should survive expansion");
}

#[test]
fn grouped_simp_expansion_preserves_resource_scalar_and_quantified_transitions() {
    let c_source = "int32 inspect(int32 p[1], int32 x) { return 0; }";
    let click_source = r#"
verifying "inspect.c";

int32 inspect(int32 p[1], int32 x) {
    requires forall (k: int32) {
        0 <= k and k < 1 implies x == x
    };
    owns p[0..1];
    immutable;
    ensures result == 0;
    ensures forall (k: int32) {
        0 <= k and k < 1 implies x == x
    };
} by {
    execute();
    frame();
    simp();
}
"#;
    let sources = [("inspect.c", c_source)];

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &sources,
        "inspect",
        CProofClaim::Grouped,
        2,
    )
    .expect("grouped simp should capture every newly closed claim");

    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the grouped transition certificate should re-verify");
}

#[test]
fn grouped_simp_expansion_uses_explicit_frame_consequences() {
    let c_source = r#"
int32 increment_and_return_old(int32 p[1]) {
    int32 result;
    result = p[0];
    p[0] = 0;
    return result;
}
"#;
    let click_source = r#"
verifying "increment.c";

int32 increment_and_return_old(int32 p[1]) {
    owns p[0..1];
    mutable p[0..1];
    ensures result == old(p[0]);
    ensures p[0] == 0;
} by {
    execute();
    frame();
    simp();
}
"#;
    let sources = [("increment.c", c_source)];

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &sources,
        "increment_and_return_old",
        CProofClaim::Grouped,
        2,
    )
    .expect("grouped simp should capture frame-dependent claims");

    assert!(!expanded.contains("simp();"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the grouped frame transition certificate should re-verify");
}

#[test]
fn expansion_preserves_unfolded_resource_and_predicate_fact_spellings() {
    let c_source = r#"
struct box {
    int32 len;
    int32 cap;
    int32* data;
};

int32 inspect(struct box* owner) {
    int32 ignored;
    return 0;
}
"#;
    let click_source = r#"
predicate terminated_at(data: int32[], length: int32) {
    data[length] == 0
}

resource owned_box(owner: struct box*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact terminated_at(owner->data, owner->len);
    fact separate(
        memory(object(owner)),
        memory(owner->data[0..owner->cap])
    );
}

verifying "inspect.c";

int32 inspect(struct box* owner) {
    consumes owned_box(owner);
    ensures result == 0;
} by {
    unfold(owned_box(owner));
    unfold(terminated_at);
    step();
    execute();
    simp();
}
"#;

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &[("inspect.c", c_source)],
        "inspect",
        CProofClaim::Grouped,
        2,
    )
    .expect("the declaration should expand with unfolded surface facts");

    // The assertions below are about the emitted `step() using` premises,
    // not the resource declaration echoed above them; scope to the block
    // so a spelling surviving only in the declaration cannot pass.
    let step_using = expanded
        .split("step() using {")
        .nth(1)
        .and_then(|rest| rest.split_once('}'))
        .map(|(block, _)| block)
        .expect("the expansion should emit a step() using block");
    assert!(
        step_using.contains("separate(memory(object(owner)), memory(owner->data[0..owner->cap]));"),
        "{expanded}"
    );
    // The aggregate premise replaces its per-field decomposition.
    assert!(
        !step_using.contains("memory(owner->len), memory(owner->data["),
        "{expanded}"
    );
    assert!(
        !step_using.contains("memory(owner->cap), memory(owner->data["),
        "{expanded}"
    );
    assert!(
        !step_using.contains("memory(owner->data), memory(owner->data["),
        "{expanded}"
    );
    // Non-call statement expansion retains its established ambient-condition
    // behavior; this issue narrows opaque-call dependencies only.
    assert!(
        step_using.contains("owner->data[owner->len] == 0;"),
        "{expanded}"
    );
    assert!(!step_using.contains("terminated_at"), "{expanded}");
    assert!(
        expanded.contains("fact terminated_at(owner->data, owner->len);"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("inspect.c", c_source)])
        .expect("the re-folded aggregate premise should re-verify");
}

#[test]
fn expanded_execute_and_frame_replay_after_resource_branch() {
    let get_source = r#"
struct vector { int32 len; int32 cap; int32* data; };
int32 vector_get(struct vector* owner, int32 index) {
    int32* data;
    data = owner->data;
    return data[index];
}
"#;
    let set_source = r#"
struct vector { int32 len; int32 cap; int32* data; };
int32 vector_set(struct vector* owner, int32 index, int32 value) {
    int32* data;
    data = owner->data;
    data[index] = value;
    return data[index];
}
"#;
    let replace_source = r#"
struct vector { int32 len; int32 cap; int32* data; };
int32 vector_replace_if(
    struct vector* owner,
    int32 index,
    int32 replacement,
    int32 replace
) {
    int32 original;
    int32 selected;
    original = vector_get(owner, index);
    if (replace != 0) {
        selected = vector_set(owner, index, replacement);
    } else {
        selected = vector_set(owner, index, original);
    }
    return selected;
}
"#;
    let click_source = r#"
resource nonempty_vector(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 1 <= owner->len;
    fact owner->len <= owner->cap;
    fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
}

verifying "vector_get.c";
verifying "vector_set.c";
verifying "vector_replace_if.c";

int32 vector_get(struct vector* owner, int32 index) {
    requires 0 <= index;
    requires index < owner->len;
    views nonempty_vector(owner);
    immutable;
    ensures result == owner->data[index];
    ensures result == old(owner->data[index]);
} by {
    execute();
    frame();
    have result == owner->data[index] by {
        normalize();
    }
    assumption();
    have result == old(owner->data[index]) by {
        assumption();
    }
    assumption();
}

int32 vector_set(struct vector* owner, int32 index, int32 value) {
    requires 0 <= index;
    requires index < owner->len;
    mutable owner->data[index..index + 1];
    owns nonempty_vector(owner);
    ensures result == value;
    ensures owner->data[index] == value;
    ensures owner->len == old(owner->len);
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
} by {
    unfold(nonempty_vector(owner));
    step();
    step();
    step();
    step() using {
        0 <= index;
        index < owner->len;
        loadable(old(owner->len));
        loadable(old(owner->cap));
        loadable(old(owner->data));
        1 <= owner->len;
        owner->len <= owner->cap;
        separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
    }
    fold(nonempty_vector(owner));
    have index < index + 1 by simp;
    frame();
    simp();
}

int32 vector_replace_if(
    struct vector* owner,
    int32 index,
    int32 replacement,
    int32 replace
) {
    requires 0 <= index;
    requires index < owner->len;
    owns nonempty_vector(owner);
    mutable owner->data[index..index + 1];
    ensures replace != 0 implies result == replacement;
} by {
    step();
    step();
    step() using {
        index < owner->len;
        0 <= index;
        1 <= owner->len;
        owner->len <= owner->cap;
        loadable(old(owner->cap));
        loadable(old(owner->data));
        loadable(old(owner->len));
    }
    have replace == replace by {
        normalize();
    }
    branch {
        then {
            step() using {
                index < owner->len;
                0 <= index;
                1 <= owner->len;
                owner->len <= owner->cap;
                replace != 0;
                loadable(old(owner->cap));
                loadable(old(owner->data));
                loadable(old(owner->len));
            }
            have replace != 0 implies selected == replacement by simp;
            have not (replace != 0) implies selected == original by simp;
            have index < index + 1 by simp;
        }
        else {
            step() using {
                index < owner->len;
                0 <= index;
                1 <= owner->len;
                owner->len <= owner->cap;
                replace == 0;
                loadable(old(owner->cap));
                loadable(old(owner->data));
                loadable(old(owner->len));
            }
            have replace != 0 implies selected == replacement by simp;
            have not (replace != 0) implies selected == original by simp;
            have index < index + 1 by simp;
        }
    }
    execute();
    have index < index + 1 by simp;
    frame();
    simp();
}
"#;
    let sources = [
        ("vector_get.c", get_source),
        ("vector_set.c", set_source),
        ("vector_replace_if.c", replace_source),
    ];
    let expanded_frame = expand_top_level_tactic_for_test(
        click_source,
        &sources,
        "vector_replace_if",
        CProofClaim::Grouped,
        7,
    )
    .expect("smart frame should expand with snapshot-correct loadability premises");

    assert!(
        expanded_frame.contains("frame() using {"),
        "{expanded_frame}"
    );
    verify_c0_sources(&expanded_frame, &sources)
        .expect("expanded frame certificate should independently replay");

    let execute_offset = expanded_frame
        .rfind("    execute();")
        .expect("common execute should exist")
        + 4;
    let execute_position = position_at_offset(&expanded_frame, execute_offset);
    let expanded_execute = expand_c0_tactic_source_at(
        &expanded_frame,
        &sources,
        execute_position.line,
        execute_position.column,
    )
    .expect("common execute should expand after a resource branch");
    verify_c0_sources(&expanded_execute, &sources)
        .expect("expanded execute certificate should independently replay");
}

#[test]
fn source_position_maps_smart_and_implicit_default_proofs() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let explicit = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
} by auto;
"#;
    assert_eq!(
        c0_tactic_source_position(
            explicit,
            &[("identity.c", c_source)],
            "identity.contract",
            0,
        )
        .unwrap(),
        SourcePosition { line: 4, column: 6 }
    );
    assert!(
        c0_tactic_source_position(
            explicit,
            &[("identity.c", c_source)],
            "identity.contract",
            2,
        )
        .is_err()
    );
    let expanded = expand_c0_tactic_source_at(explicit, &[("identity.c", c_source)], 4, 6)
        .expect("an internal smart-proof timing should select the whole source proof");
    assert!(!expanded.contains("by auto"));
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the expanded smart proof should verify");

    let implicit = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
}
"#;
    assert_eq!(
        c0_tactic_source_position(
            implicit,
            &[("identity.c", c_source)],
            "identity.ensures_0",
            0,
        )
        .unwrap(),
        SourcePosition { line: 3, column: 5 }
    );
    assert!(
        c0_tactic_source_position(
            implicit,
            &[("identity.c", c_source)],
            "identity.ensures_0",
            2,
        )
        .is_err()
    );
}

#[test]
fn expanded_uint8_facts_print_as_parseable_typed_literals() {
    let c_source = "int32 contains(uint8 p[], int32 n) { return 0; }";
    let click_source = r#"verifying "contains.c";
int32 contains(uint8 p[], int32 n) {
    requires loadable(p[0..n]);
    requires has_x: bytes_contains(p, 0, n, 'x');
    ensures bytes_contains(p, 0, n, 'x') by {
        execute();
        unfold(bytes_contains);
        choose(found from requirement has_x);
        witness(k = found);
        simp();
    }
}"#;
    let offset = click_source.rfind("simp").expect("simp should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("contains.c", c_source)],
        position.line,
        position.column,
    )
    .expect("uint8 proposition should expand");

    assert!(expanded.contains("bytes_contains(p, 0, n, 120u8)"));
    verify_c0_sources(&expanded, &[("contains.c", c_source)])
        .expect("printed uint8 literal should parse and re-verify");
}

#[test]
fn expanded_bitvector_facts_print_parseable_negative_literals() {
    let c_source = "int32 all_bits() { return ~0; }";
    let click_source = r#"verifying "all_bits.c";
int32 all_bits() {
    ensures result == 4294967295 by auto;
}"#;
    let offset = click_source.find("auto").expect("auto should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("all_bits.c", c_source)],
        position.line,
        position.column,
    )
    .expect("bitvector proposition should expand");

    assert!(expanded.contains("result == -1"));
    verify_c0_sources(&expanded, &[("all_bits.c", c_source)])
        .expect("printed negative literal should parse and re-verify");
}

#[test]
fn expanded_branch_certificate_uses_the_branch_entry_state() {
    let c_source = r#"int32 compare_swap2(int32 p[2]) {
    int32 tmp;
    if (p[1] < p[0]) {
        tmp = p[0];
        p[0] = p[1];
        p[1] = tmp;
    } else {
        tmp = 0;
    }
    return 0;
}"#;
    let click_source = r#"verifying "compare_swap2.c";
predicate sorted_pair(p: int32[2]) {
    p[0] <= p[1]
}
int32 compare_swap2(int32 p[2]) {
    requires loadable(p[0..2]);
    consumes p[0..2];
    ensures sorted_pair(p) by {
        execute();
        unfold(sorted_pair);
        simp();
    }
}"#;
    let offset = click_source.rfind("simp").expect("simp should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("compare_swap2.c", c_source)],
        position.line,
        position.column,
    )
    .expect("post-execution simp should expand");

    assert!(expanded.contains("if at(function.entry, p[1])"));
    verify_c0_sources(&expanded, &[("compare_swap2.c", c_source)])
        .expect("branch certificate should replay against the state where it branched");
}

#[test]
fn expanded_contract_let_facts_remain_source_indexable() {
    let c_source = "int32 increment(int32 x) { return x + 1; }";
    let click_source = r#"verifying "increment.c";
int32 increment(int32 x) {
    let max: int32 = 2147483647;
    let expected = x + 1;
    requires x < max;
    ensures result_value: result == expected by auto;
}"#;
    let offset = click_source.find("auto").expect("auto should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("increment.c", c_source)],
        position.line,
        position.column,
    )
    .expect("contract-let proof should expand");

    assert!(expanded.contains("(let max = 2147483647; 2147483647)"));
    verify_c0_sources(&expanded, &[("increment.c", c_source)])
        .expect("parenthesized contract lets should re-verify");
    c0_tactic_source_position(
        &expanded,
        &[("increment.c", c_source)],
        "increment.result_value",
        0,
    )
    .expect("semicolons inside contract lets must not split source tactics");
}

#[test]
fn expanded_post_execution_apply_retains_its_facts_for_the_closer() {
    let c_source = "int32 inspect(uint8 p[], int32 len) { return 0; }";
    let click_source = r#"verifying "inspect.c";
int32 inspect(uint8 p[], int32 len) {
    requires loadable(p[0..len + 1]);
    requires exact: cstr_len(p, len);
    ensures 0 <= len by {
        execute();
        apply(cstr_len_nonnegative(p, len));
        simp();
    }
}"#;
    let offset = click_source.find("apply").expect("apply should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("inspect.c", c_source)],
        position.line,
        position.column,
    )
    .expect("post-execution apply should expand");

    assert!(expanded.contains("apply(cstr_len_nonnegative(p, len)) using"));
    verify_c0_sources(&expanded, &[("inspect.c", c_source)])
        .expect("explicit apply conclusions should remain available to the trailing simp");
}

#[test]
fn expansion_retains_callees_used_by_an_earlier_claim() {
    let callee_source = r#"int32 set_cell(int32 p[], int32 value) {
    p[0] = value;
    return value;
}"#;
    let caller_source = r#"int32 set_then_read(int32 p[], int32 value) {
    int32 ignored;
    ignored = set_cell(p, value);
    return p[0];
}"#;
    let click_source = r#"verifying "set_cell.c";
verifying "set_then_read.c";
int32 set_cell(int32 p[], int32 value) {
    owns p[0..1] by auto;
    mutable p[0..1] by { execute(); frame(); }
    ensures p[0] == value by auto;
    ensures result == value by auto;
}
int32 set_then_read(int32 p[], int32 value) {
    owns p[0..1] by {
        step();
        step();
        step();
    }
    ensures result == value by {
        step();
        step();
        step();
        simp();
    }
}"#;
    let sources = [
        ("set_cell.c", callee_source),
        ("set_then_read.c", caller_source),
    ];
    let position = c0_tactic_source_position(click_source, &sources, "set_then_read.ensures_1", 0)
        .expect("later claim should have a source tactic");
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("selected later-claim tactic should expand with the callee available");

    verify_c0_sources(&expanded, &sources)
        .expect("expanded later claim should re-verify with its earlier claim");
}

#[test]
fn expands_a_deferred_tactic_in_one_nested_proof_branch() {
    let c_source = r#"int32 nested(int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
        if (y > 0) { y = y + 1; } else { y = 0; }
    } else {
        y = 0;
    }
    return y;
}"#;
    let click_source = r#"verifying "nested.c";
int32 nested(int32 x) {
    requires x < 2147483647;
    ensures result >= 0 by {
        step();
        if x >= 0 {
            step();
            step();
            if y > 0 {
                step();
                step();
                step();
                simp();
            } else {
                step();
                step();
                step();
                simp();
            }
        } else {
            step();
            step();
            step();
            simp();
        }
    }
}"#;
    let needle = "step();\n                step();\n                step();\n                simp";
    let offset = click_source
        .find(needle)
        .map(|start| start + needle.rfind("simp").unwrap())
        .expect("inner else simp should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("nested.c", c_source)],
        position.line,
        position.column,
    )
    .expect("selected nested-branch simp should expand");

    assert_eq!(expanded.matches("simp();").count(), 2);
    verify_c0_sources(&expanded, &[("nested.c", c_source)])
        .expect("sibling proof cases must not steal the deferred capture");
}

#[test]
fn expanded_symbolic_range_propositions_use_parser_syntax() {
    let c_source = "int32 identity(int32 x, int32 n) { return x; }";
    let click_source = r#"verifying "identity.c";
int32 identity(int32 x, int32 n) {
    requires (0..n).any(|k| { k == x });
    ensures same_any: (0..n).any(|k| { k == x }) by auto;
}"#;
    let offset = click_source.find("auto").expect("auto should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("identity.c", c_source)],
        position.line,
        position.column,
    )
    .expect("symbolic range proposition should expand");

    assert!(expanded.contains("(0..n).any(|k| { k == x })"));
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("printed symbolic range proposition should re-verify");
}

#[test]
fn expands_single_smart_and_default_function_proofs_by_source_location() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let smart = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x by { execute(); simp(); }
}
"#;
    let smart_position = position_at_offset(smart, smart.find("simp").unwrap());
    let smart_expanded = expand_c0_tactic_source_at(
        smart,
        &[("identity.c", c_source)],
        smart_position.line,
        smart_position.column,
    )
    .expect("single smart proof should expand as a whole proof");
    assert!(smart_expanded.contains("execute();"));
    assert!(!smart_expanded.contains("simp();"));
    verify_c0_sources(&smart_expanded, &[("identity.c", c_source)]).unwrap();

    let implicit = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
}
"#;
    let implicit_position = position_at_offset(implicit, implicit.find("ensures").unwrap());
    let implicit_expanded = expand_c0_tactic_source_at(
        implicit,
        &[("identity.c", c_source)],
        implicit_position.line,
        implicit_position.column,
    )
    .expect("default proof should expand from its clause coordinate");
    assert!(implicit_expanded.contains("ensures result == x by {"));
    verify_c0_sources(&implicit_expanded, &[("identity.c", c_source)]).unwrap();
}

#[test]
fn whole_function_proof_expansion_skips_unrelated_broken_proofs() {
    let good_c = "int32 good(int32 x) { return x; }";
    let bad_c = "int32 bad(int32 x) { return x; }";
    let click_source = r#"verifying "good.c";
verifying "bad.c";
int32 good(int32 x) {
    ensures result == x;
}
int32 bad(int32 x) {
    ensures result == x + 1 by simp;
}
"#;
    let sources = [("good.c", good_c), ("bad.c", bad_c)];
    verify_c0_sources(click_source, &sources)
        .expect_err("the unrelated bad proof should fail complete verification");
    let selected = position_at_offset(click_source, click_source.find("ensures").unwrap());

    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, selected.line, selected.column)
            .expect("whole-proof expansion should verify only the selected function");

    assert!(expanded.contains("ensures result == x by {"));
    verify_c0_sources_at(&expanded, &sources, selected.line, selected.column)
        .expect("the expanded selected function should verify independently");
}

#[test]
fn partial_tactic_expansion_skips_unrelated_broken_proofs() {
    let good_c = "int32 good(int32 x) { return x; }";
    let bad_c = "int32 bad(int32 x) { return x; }";
    let click_source = r#"verifying "good.c";
verifying "bad.c";
int32 good(int32 x) {
    ensures result == x by { execute(); simp(); }
}
int32 bad(int32 x) {
    ensures result == x + 1 by simp;
}
"#;
    let sources = [("good.c", good_c), ("bad.c", bad_c)];
    verify_c0_sources(click_source, &sources)
        .expect_err("the unrelated bad proof should fail complete verification");
    let selected_offset = click_source.find("execute();").unwrap();
    let selected = position_at_offset(click_source, selected_offset);

    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, selected.line, selected.column)
            .expect("partial expansion should verify only the selected function");

    assert_ne!(expanded, click_source);
    assert_eq!(
        &expanded[..selected_offset],
        &click_source[..selected_offset]
    );
    let unselected_suffix = &click_source[selected_offset + "execute();".len()..];
    assert!(expanded.ends_with(unselected_suffix));
    let relocated = c0_tactic_source_position(&expanded, &sources, "good.ensures_0", 0).unwrap();
    verify_c0_sources_at(&expanded, &sources, relocated.line, relocated.column)
        .expect("the expanded selected function should verify independently");
    verify_c0_sources(&expanded, &sources)
        .expect_err("whole-file verification should still see the unrelated failure");
}

#[test]
fn tactic_expansion_reports_required_dependency_path() {
    let callee_c = "int32 callee(int32 x) { return x; }";
    let caller_c = "int32 caller(int32 x) { int32 result; result = callee(x); return result; }";
    let click_source = r#"verifying "callee.c";
verifying "caller.c";
int32 callee(int32 x) {
    ensures result == x + 1 by { execute(); simp(); }
}
int32 caller(int32 x) {
    ensures result == x by { execute(); simp(); }
}
"#;
    let sources = [("callee.c", callee_c), ("caller.c", caller_c)];
    let selected = position_at_offset(click_source, click_source.rfind("execute();").unwrap());

    let error = expand_c0_tactic_source_at(click_source, &sources, selected.line, selected.column)
        .expect_err("a broken required dependency must block expansion");

    assert!(
        error.message().contains("caller -> callee"),
        "{}",
        error.message()
    );
}

#[test]
fn expands_selected_tactics_in_branched_execution_by_path() {
    let c_source = r#"int32 write_selected(int32 p[2], int32 flag) {
    if (flag) {
        p[0] = 1;
        return 0;
    } else {
        p[1] = 1;
        return 1;
    }
}"#;
    let click_source = r#"verifying "write_selected.c";
int32 write_selected(int32 p[2], int32 flag) {
    consumes p[0..2];
    mutable p[0..2];
    ensures result == 0 or result == 1;
} by {
    execute();
    if result == 0 {
        have result + 1 == 1 by simp;
        frame();
    } else {
        have result - 1 == 0 by simp;
        frame();
    }
    simp();
}
"#;
    let sources = [("write_selected.c", c_source)];
    verify_c0_sources(click_source, &sources).expect("branched baseline should verify");
    for (selected_text, selected_smart) in [
        ("have result + 1", "have result + 1 == 1 by simp"),
        ("have result - 1", "have result - 1 == 0 by simp"),
    ] {
        let selected_offset = click_source.find(selected_text).unwrap();
        let selected = position_at_offset(click_source, selected_offset);

        let expanded =
            expand_c0_tactic_source_at(click_source, &sources, selected.line, selected.column)
                .expect("one branch's smart have should expand by its execution path");

        assert!(!expanded.contains(selected_smart));
        assert!(expanded.contains("if result == 0"));
        verify_c0_sources(&expanded, &sources)
            .expect("path-aligned branch expansion should replay as a complete proof");
    }
}

#[test]
fn pure_theorem_expansion_is_certificate_backed_and_idempotent() {
    let source = r#"theorem incremented_zero_is_one(before: int32, after: int32) {
    requires before == 0;
    requires after == before + 1;
    ensures after == 1 by {
        rewrite(after == before + 1);
        rewrite(before == 0);
        simp();
    }
}
"#;
    let expanded_once = expand_pure_theorem_source(source, &[], "incremented_zero_is_one", 0)
        .expect("smart theorem script should expand");
    let expanded_twice =
        expand_pure_theorem_source(&expanded_once, &[], "incremented_zero_is_one", 0)
            .expect("expanded theorem certificate should expand again");

    assert!(!expanded_once.contains("simp"));
    assert_eq!(expanded_once, expanded_twice);
    let verified =
        verify_click_theorems(&expanded_once).expect("expanded theorem should re-verify");
    verified[0]
        .proof_certificate()
        .expect("expanded theorem should retain a surface certificate");
}

#[test]
fn pure_mixed_linear_smart_script_expands_the_retained_proof_object_path() {
    let source = r#"
        theorem required(x: int32) {
            requires x >= 0;
            ensures x >= 0 by auto;
        }

        theorem applied_then_simp(x: int32) {
            requires (x >= 0) and (x <= 10);
            ensures (x >= 0) and (x >= 0) by {
                extract(x >= 0);
                apply(required(x));
                simp();
            }
        }
    "#;
    let expanded = expand_pure_theorem_source(source, &[], "applied_then_simp", 0)
        .expect("the checked pure theorem path should expand");
    let selected = &expanded[expanded
        .find("theorem applied_then_simp")
        .expect("expanded source should retain the selected theorem")..];
    assert!(
        selected.contains("apply(required(x)) using {"),
        "{selected}"
    );
    assert!(selected.contains("x >= 0;"), "{selected}");
    assert!(selected.contains("extract(x >= 0);"), "{selected}");
    assert!(selected.contains("split();"), "{selected}");
    assert!(!selected.contains("apply(required(x));"), "{selected}");
    assert!(!selected.contains("simp();"), "{selected}");
    verify_click_theorems(&expanded)
        .expect("the serialized pure theorem certificate should independently reverify");
}

#[test]
fn pure_branch_local_apply_expands_the_retained_proof_object_paths() {
    let source = r#"
        theorem equality_case(x: int32) {
            requires x == 0;
            ensures x == 0 or not (x == 0) by {
                left();
            }
        }

        theorem inequality_case(x: int32) {
            requires not (x == 0);
            ensures x == 0 or not (x == 0) by {
                right();
            }
        }

        theorem branch_apply(x: int32) {
            ensures x == 0 or not (x == 0) by {
                if x == 0 {
                    apply(equality_case(x));
                    simp();
                } else {
                    apply(inequality_case(x));
                    simp();
                }
            }
        }
    "#;
    let expanded = expand_pure_theorem_source(source, &[], "branch_apply", 0)
        .expect("the checked branch-local theorem paths should expand");
    let selected = &expanded[expanded
        .find("theorem branch_apply")
        .expect("expanded source should retain the selected theorem")..];
    assert!(
        selected.contains("apply(equality_case(x)) using {"),
        "{selected}"
    );
    assert!(
        selected.contains("apply(inequality_case(x)) using {"),
        "{selected}"
    );
    assert!(!selected.contains("simp();"), "{selected}");
    verify_click_theorems(&expanded)
        .expect("the serialized branch-local certificates should independently reverify");
}

#[test]
fn expands_qualified_frame_tactic() {
    let c_source = r#"int32 set_cell(int32 p[], int32 value) {
    p[0] = value;
    return value;
}"#;
    let click_source = r#"verifying "set_cell.c";
int32 set_cell(int32 p[], int32 value) {
    owns p[0..1] by auto;
    mutable p[0..1] by { execute(); frame(function); }
}
"#;
    let sources = [("set_cell.c", c_source)];
    verify_c0_sources(click_source, &sources).expect("qualified frame baseline should verify");
    let selected_offset = click_source
        .find("frame(function)")
        .expect("qualified frame should exist");
    let position = position_at_offset(click_source, selected_offset);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("qualified frame should expand");

    assert!(!expanded.contains("frame(function);"), "{expanded}");
    assert!(expanded.contains("frame(function) using {"), "{expanded}");
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!("expanded qualified frame should replay:\n{error:?}\n{expanded}")
    });
}
