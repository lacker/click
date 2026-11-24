use super::*;

const PROOF: &str = r#"verifying "count.c";
int32 count(int32 n) {
 requires 0 <= n and n <= 1000;
 ensures result == n;
} by {
 step_until(loop(0).entry);
 loop {
  decreases n-i;
  invariant 0 <= i and i <= n;
  maintain by { step_until(loop.back_edge);  }
 }
 step_until(function.exit); close();
}"#;
fn source(body: &str) -> String {
    format!("int32 count(int32 n) {{ int32 i; i=0; while(i<n) {{ {body} }} return i; }}")
}
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn back_edge_checks_body_end_and_continue_and_expands() {
    for body in ["i=i+1;", "i=i+1; continue;"] {
        let c = source(body);
        let sources = [("count.c", c.as_str())];
        let verified_for_expansion = verify_c_sources(PROOF, &sources).unwrap();
        let expanded =
            expand_checked_grouped_claim(PROOF, &verified_for_expansion, "count").unwrap();
        verify_c_sources(&expanded, &sources).unwrap();
    }
}
#[test]
fn back_edge_rejects_exits_wrong_phase_and_false_invariants() {
    for body in [
        "break;",
        "return i;",
        "i=i+2;",
        "if (i == 0) { i=i+1; } else { i=i+1; }",
    ] {
        assert!(verify_c_sources(PROOF, &[("count.c", &source(body))]).is_err());
    }
    let c = source("i=i+1;");
    for proof in [
        PROOF.replacen(
            "step_until(loop(0).entry);",
            "step_until(loop.back_edge);",
            1,
        ),
        PROOF.replace("decreases n-i;", "decreases i;"),
    ] {
        assert!(verify_c_sources(&proof, &[("count.c", &c)]).is_err());
    }
}
#[test]
fn back_edge_parses_and_preserves_bare_labels() {
    let parsed = parse(PROOF).unwrap();
    assert!(!parsed.function_blocks().is_empty());
    for old_target in ["back_edge()", "loop(0).back_edge()", "loop(0)"] {
        assert!(parse(&PROOF.replace("loop.back_edge", old_target)).is_err());
    }
    assert!(parse(&PROOF.replace("loop.back_edge", "loop(0).back_edge")).is_ok());
    assert!(parse(&PROOF.replace("loop.back_edge", "loop(0).exit")).is_err());
    let labeled = PROOF.replace(
        "step_until(loop.back_edge);",
        "mark back_edge; step_until(back_edge.entry);",
    );
    assert!(parse(&labeled).is_ok());
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/surface/tests/back_edge_tests.rs");
}
