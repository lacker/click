use super::*;

const PROOF: &str = r#"verifying "count.c";
int32 count(int32 n) {
 requires 0 <= n and n <= 1000;
 ensures result == n;
} by {
 execute_until(loop(0));
 loop {
  decreases n-i;
  invariant 0 <= i and i <= n;
  preserve by { execute_until(back_edge()); close_invariants(); }
 }
 execute(); simp();
}"#;
fn source(body: &str) -> String {
    format!("int32 count(int32 n) {{ int32 i; i=0; while(i<n) {{ {body} }} return i; }}")
}
#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn back_edge_checks_body_end_and_continue_and_expands() {
    for body in ["i=i+1;", "i=i+1; continue;"] {
        let c = source(body);
        let sources = [("count.c", c.as_str())];
        verify_c0_sources(PROOF, &sources).unwrap();
        let expanded =
            expand_c0_claim_source(PROOF, &sources, "count", CProofClaim::Grouped).unwrap();
        verify_c0_sources(&expanded, &sources).unwrap();
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
        assert!(verify_c0_sources(PROOF, &[("count.c", &source(body))]).is_err());
    }
    let c = source("i=i+1;");
    for proof in [
        PROOF.replacen("execute_until(loop(0));", "execute_until(back_edge());", 1),
        PROOF.replace(
            "close_invariants();",
            "execute_until(back_edge()); close_invariants();",
        ),
        PROOF.replace("decreases n-i;", "decreases i;"),
    ] {
        assert!(verify_c0_sources(&proof, &[("count.c", &c)]).is_err());
    }
}
#[test]
fn back_edge_parses_and_preserves_bare_labels() {
    let parsed = parse(PROOF).unwrap();
    assert!(!parsed.function_blocks().is_empty());
    assert!(parse(&PROOF.replace("back_edge()", "back_edge(1)")).is_err());
    let labeled = PROOF.replace(
        "execute_until(back_edge());",
        "mark back_edge; execute_until(back_edge);",
    );
    assert!(parse(&labeled).is_ok());
}
#[test]
#[ignore = "nightly: 1.8s in the parallel gate"]
fn back_edge_work_scales_with_body_size() {
    let samples = [8, 128, 1024].map(|size| {
        let body = "i=i;".repeat(size) + "i=i+1;";
        let c = source(&body);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            verify_c0_sources(PROOF, &[("count.c", &c)])
        });
        result.unwrap();
        (size, work)
    });
    assert!(samples[0].1 > 0);
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * (pair[1].0 / pair[0].0) * 3,
            "{samples:?}"
        );
    }
}
