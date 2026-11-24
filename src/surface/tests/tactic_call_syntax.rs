use super::*;

#[test]
fn smart_proof_calls_have_identical_meaning_with_optional_braces() {
    for tactic in ["close", "normalize"] {
        let call = format!("by {tactic}();");
        let block = format!("by {{ {tactic}(); }}");
        let source = |proof: &str| {
            format!(
                "verifying \"identity.c\"; int32 identity(int32 x) {{ ensures result == x {proof} }}"
            )
        };
        assert_eq!(
            parser::parse(&source(&call)).unwrap().function_blocks(),
            parser::parse(&source(&block)).unwrap().function_blocks(),
            "{tactic}: braces must only delimit the same one-tactic proof"
        );
        let goal = if tactic == "normalize" {
            "7 == 7"
        } else {
            "x == 7"
        };
        for proof in [&call, &block] {
            verify_click_theorems(&format!(
                "theorem fact(x: int32) {{ requires x == 7; ensures {goal} {proof} }}"
            ))
            .unwrap_or_else(|error| panic!("{proof}: {error:?}"));
        }
    }
}

#[test]
fn bare_smart_tactics_are_rejected_in_proofs_and_scripts() {
    for proof in [
        "by close;",
        "by { close; }",
        "by { have x == 7 by close(); close; }",
        "by { have x == 7 by close; close(); }",
        "by close using { x == 7; };",
    ] {
        let source =
            format!("theorem fact(x: int32) {{ requires x == 7; ensures x == 7 {proof} }}");
        let error = parser::parse(&source).expect_err(proof);
        assert!(
            error.message().contains("requires parentheses"),
            "{proof}: {error:?}"
        );
    }
    for proof in ["by close(1);", "by { close(1); }"] {
        let error =
            parser::parse(&format!("theorem fact() {{ ensures true {proof} }}")).unwrap_err();
        assert!(
            error.message().contains("no arguments"),
            "{proof}: {error:?}"
        );
    }
}

#[test]
fn nested_single_tactic_calls_keep_their_checked_scopes() {
    verify_click_theorems(
        "theorem fact(x: int32) {
        requires x == 7;
        ensures x == 7 by {
            have first: x == 7;
            have second: x == 7 by { close(); }
            have x == 7 by close();
            close() using { first; second; };
        }
    }",
    )
    .unwrap();
}

#[test]
fn close_cannot_be_shadowed_by_a_user_tactic() {
    let error = parser::parse("tactic close() { ensures true; } by close();").unwrap_err();
    assert!(error.message().contains("built-in"), "{error:?}");
}

#[test]
fn canonical_using_calls_wrap_long_premises_and_keep_their_terminator() {
    let left = "first_parameter_with_a_descriptive_mathematical_name";
    let right = "second_parameter_with_a_descriptive_mathematical_name";
    let head = format!(
        "theorem equal({left}: Integer, {right}: Integer) {{ requires {left} == {right}; ensures {left} == {right}"
    );
    let source = format!("{head} by {{ close() using {{ {left} == {right}; }} }} }}");
    verify_click_theorems(&source).unwrap();
    let parsed = parser::parse(&source).unwrap();
    let proof = parsed.theorem_definitions()[0].ensures()[0].proof();
    let printed = super::super::printing::format_partial_tactic_sequence(proof.tactics().unwrap());
    assert!(printed.ends_with("};"), "{printed}");
    assert!(printed.lines().all(|line| line.len() <= 100), "{printed}");
    assert!(printed.contains("\n        "), "{printed}");
    let rewritten = format!("{head} by {{ {printed} }} }}");
    let reparsed = parser::parse(&rewritten).unwrap();
    assert_eq!(
        proof,
        reparsed.theorem_definitions()[0].ensures()[0].proof()
    );
    verify_click_theorems(&rewritten).unwrap();
}

#[test]
fn binary_splits_use_their_own_join_interface_syntax() {
    let source = |body: &str| {
        format!("verifying \"split.c\"; int32 split(int32 x) {{ ensures true by {{ {body} }} }}")
    };
    for (head, arms, interface_separator) in [
        ("if x == 0", "{ close(); } else { close(); }", "then "),
        (
            "branch",
            "{ true => { close(); } false => { close(); } }",
            "",
        ),
    ] {
        for interface in [
            "".to_string(),
            format!("ensuring {{ fact x == x; }} {interface_separator}"),
        ] {
            let written = source(&format!("{head} {interface}{arms}"));
            let parsed = parser::parse(&written).unwrap();
            let proof = parsed.function_blocks()[0].ensures()[0].proof();
            let printed =
                super::super::printing::format_partial_tactic_sequence(proof.tactics().unwrap());
            assert_eq!(
                printed.contains("then {"),
                !interface.is_empty() && !interface_separator.is_empty(),
                "{printed}"
            );
            let reparsed = parser::parse(&source(&printed)).unwrap();
            assert_eq!(proof, reparsed.function_blocks()[0].ensures()[0].proof());
        }
        assert!(parser::parse(&source(&format!("{head} then {arms}"))).is_err());
        let wrong_separator = if interface_separator.is_empty() {
            "then "
        } else {
            ""
        };
        let error = parser::parse(&source(&format!(
            "{head} ensuring {{ fact x == x; }} {wrong_separator}{arms}"
        )))
        .unwrap_err();
        assert!(error.message().contains("then"), "{error:?}");
    }
}

/// The parser names the replacement for a removed spelling in scripts and
/// one-tactic proofs.
#[test]
fn removed_tactic_spellings_name_their_replacement() {
    for (proof, replacement) in [
        ("by assumption();", "`close()`"),
        ("by { assumption(); }", "`close()`"),
        ("by auto();", "the omitted proof"),
        ("by { auto(); }", "the omitted proof"),
        (
            "by { have x == 7 by auto(); close(); }",
            "the omitted proof",
        ),
        ("by arithmetic();", "`close() using {}`"),
        (
            "by { arithmetic() using { x == 7; }; }",
            "`close() using { ... }`",
        ),
        ("by known();", "`close()`"),
        ("by { known(); }", "`close()`"),
        ("by solve();", "`close()`"),
        ("by { solve(); }", "`close()`"),
        ("by solve() using { x == 7; };", "`close() using { ... }`"),
        (
            "by { solve() using { x == 7; } }",
            "`close() using { ... }`",
        ),
        ("by { execute_until(function.exit); }", "`step_until`"),
    ] {
        let source =
            format!("theorem fact(x: int32) {{ requires x == 7; ensures x == 7 {proof} }}");
        let error = parser::parse(&source).expect_err(proof);
        assert!(error.message().contains(replacement), "{proof}: {error:?}");
    }
}
