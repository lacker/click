use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/function-pointers/callback.click");

fn function_pointer_project() -> Project {
    let p = Project::from_fixture("design/charon-trial/function-pointers");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    p
}

#[test]
fn callable_signature_mismatch_displays_both_signatures() {
    let p = function_pointer_project();
    let prepared = p.prepared().unwrap();
    let mismatched = SIDECAR
        .replacen("f: fn(i32) -> i32", "f: fn(u32) -> u32", 1)
        .replacen("    requires Doubling(f);\n", "", 1);
    let error = ProgramVerificationSession::new_program_prepared(&mismatched, &prepared)
        .err()
        .expect("the callable signature mismatch must be refused");
    assert!(
        error
            .message()
            .contains(".click has uint32 (*)(uint32) f, C has int32 (*)(int32) f"),
        "{}",
        error.message()
    );
    assert!(
        !error.message().contains("FunctionPointer("),
        "{}",
        error.message()
    );
}

// `apply` calls through `f` under the contract it requires of `f`, `relay`
// forwards its own `f` to `apply`, and `caller` and `forward` pass `twice`,
// whose own contract meets that contract. Each piece is needed.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn charon_calls_through_a_function_pointer_meet_its_named_contract() {
    let p = function_pointer_project();
    let prepared = p.prepared().unwrap();
    ProgramVerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    let twice = "fn function_pointers::twice(x: i32) -> i32 {\n    requires 0 <= x and x <= 1000;\n    ensures result == x + x;";
    let doubling = "contract fn Doubling(x: i32) -> i32 {\n    requires 0 <= x and x <= 1000;\n    ensures result == x + x;";
    // `relay` forwards `f` to `apply`, which requires the contract of it.
    let relay = "fn function_pointers::relay(f: fn(i32) -> i32, x: i32) -> i32 {\n    requires Doubling(f);\n";
    // Keep the original full positive check. Select complete function
    // proofs for local failures; declaration/interface boundary cases
    // retain their original whole-module checks.
    for (head, before, after, expected) in [
        (
            Some("fn function_pointers::apply("),
            "    requires Doubling(f);\n",
            "",
            "call through function pointer",
        ),
        (
            Some("fn function_pointers::relay("),
            relay,
            &relay.replace("    requires Doubling(f);\n", ""),
            "requires an explicit prerequisite proof (precondition clause 1 of",
        ),
        (
            Some("fn function_pointers::caller("),
            twice,
            &twice.replace("ensures result == x + x;", "ensures result >= 0;"),
            "does not satisfy named contract `Doubling`",
        ),
        (
            Some("fn function_pointers::apply("),
            doubling,
            &doubling.replace("x + x;", "x + x + 1;"),
            "unclosed goal",
        ),
    ] {
        let invalid = SIDECAR.replace(before, after);
        assert_ne!(invalid, SIDECAR);
        let error = if let Some(head) = head {
            verify_rust_proof_after(&invalid, &prepared, head)
                .expect_err("a missing or unmet callback contract must fail")
        } else {
            ProgramVerificationSession::new_program_prepared(&invalid, &prepared)
                .err()
                .expect("a missing or unmet callback contract must fail")
        };
        assert!(format!("{error:?}").contains(expected), "{error:?}");
    }
}

#[cfg(not(feature = "fast-gate"))]
#[test]
#[ignore = "nightly: 3.7s in the parallel gate"]
fn charon_function_pointer_tools_recheck_expanded_certificates() {
    let p = function_pointer_project();
    for command in ["profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "__rust_q_I17_function_pointers_I5_apply.ensures_0",
        "__rust_q_I17_function_pointers_I6_caller.ensures_0",
        "__rust_q_I17_function_pointers_I5_relay.ensures_0",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
    }
    assert_cli(&p, &["verify"]);
}

// A crate function that meets a named contract only by an explicit proof gets
// a suggested refinement theorem in Rust spelling, `Doubling(crate::twice)`,
// which verifies as suggested; a function that does not meet the contract is
// refused by the same theorem.
#[test]
fn charon_refinement_theorems_name_crate_functions_as_values() {
    let p = function_pointer_project();
    let prepared = p.prepared().unwrap();
    let twice = "fn function_pointers::twice(x: i32) -> i32 {\n    requires 0 <= x and x <= 1000;";
    let equivalent = SIDECAR.replacen(
        twice,
        "fn function_pointers::twice(x: i32) -> i32 {\n    requires 0 <= x and x <= 2000 and x <= 1000;",
        1,
    );
    let error = ProgramVerificationSession::new_program_prepared(&equivalent, &prepared)
        .err()
        .expect("an inexact contract needs an explicit refinement proof");
    let theorem = "theorem twice_is_doubling() {\n    ensures Doubling(function_pointers::twice) by {\n        unfold(Doubling(function_pointers::twice));\n        close();\n    }\n}";
    let shown = click::languages::rust::names::display_rust_names(error.message()).into_owned();
    assert!(shown.contains(theorem), "{shown}");
    let applied = |sidecar: &str| {
        let mut sidecar = sidecar.to_string();
        for caller in ["caller", "forward"] {
            let head = format!(
                "fn function_pointers::{caller}(x: i32) -> i32 {{\n    requires 0 <= x and x <= 1000;\n    ensures result == x + x;\n}}"
            );
            assert!(sidecar.contains(&head), "{caller}");
            sidecar = sidecar.replacen(
                &head,
                &format!("{head} by {{ apply(twice_is_doubling()); }}"),
                1,
            );
        }
        format!("{sidecar}\n{theorem}\n")
    };
    ProgramVerificationSession::new_program_prepared(&applied(&equivalent), &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    let weaker = SIDECAR.replacen(twice, &format!("{twice}\n    requires x != 7;"), 1);
    let error = ProgramVerificationSession::new_program_prepared(&applied(&weaker), &prepared)
        .err()
        .expect("a function that does not meet the contract is refused");
    assert!(
        error.message().contains("twice_is_doubling"),
        "{}",
        error.message()
    );
}
