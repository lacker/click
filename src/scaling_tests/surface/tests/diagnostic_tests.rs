// Scaling tests of `src/surface/tests/diagnostic_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

#[cfg(not(feature = "fast-gate"))]
use super::*;

#[test]
fn loop_back_edge_prepares_written_invariants_once_and_closes_by_exact_facts() {
    use crate::instrumentation::{IMPLICIT_LOOP_CLOSER_TACTIC, VerificationEvent, collect};

    let c_source = "int once(int i, int x) { while (i != 0) i = 0; return i; }";
    let proof = r#"
verifying "once.c";
int32 once(int32 i, int32 x) {
    requires i >= 0;
    ensures result == 0;
} by {
    loop {
        decreases i;
        invariant i >= 0;
        initialize by { close(); }
        maintain by {
            step();
            have i >= 0 by { close(); }
        }
    }
    step();
    close();
}
"#;
    let work = [2, 16, 64].map(|size| {
        let ambient = (1..=size)
            .map(|value| format!("    requires x != {value};\n"))
            .collect::<String>();
        let proof = proof.replace("    ensures", &format!("{ambient}    ensures"));
        let (verified, events) =
            collect(|| crate::surface::verify_c_sources(&proof, &[("once.c", c_source)]));
        verified.unwrap();
        let back_edge = events
            .iter()
            .skip_while(|event| {
                !matches!(event, VerificationEvent::TacticStarted(tactic)
                    if tactic.tactic_name == IMPLICIT_LOOP_CLOSER_TACTIC && tactic.claim == "once.contract")
            })
            .take_while(|event| {
                !matches!(event, VerificationEvent::TacticFinished { tactic, .. }
                    if tactic.tactic_name == IMPLICIT_LOOP_CLOSER_TACTIC)
            });
        let operations = back_edge
            .filter_map(|event| match event {
                VerificationEvent::OperationFinished { name, work, .. } => {
                    Some((name.as_str(), *work))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        for name in [
            "invariant bundle: rebind resources",
            "invariant obligations: lower declaration",
            "close invariants: exact facts",
        ] {
            assert_eq!(
                operations.iter().filter(|(label, _)| *label == name).count(),
                1,
                "{name} at {size}: {operations:?}"
            );
        }
        assert!(!operations.iter().any(|(name, _)| *name == "close invariants: member planning"));
        operations.iter().find(|(name, _)| *name == "close invariants: exact facts").unwrap().1
    });
    assert_eq!(work, [work[0]; 3]);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: growing generated loop-bundle expansion and checked work"]
fn wide_loop_invariant_bundle_expansion_work_scales_with_members() {
    let mut samples = Vec::new();
    for size in [32, 48, 64] {
        let (source, proof) = wide_loop_invariant_fixture(size);
        let sources = [("bundle.c", source.as_str())];
        // Expansion constructs a checked proof of the original claim. Retain
        // the independent cold check of its output below without first running
        // the same original claim a second time.
        let (expanded, work) = crate::instrumentation::measure_deterministic_work(|| {
            eprintln!("wide loop bundle size {size}: expand");
            crate::surface::expand_c_claim_source_by_label(&proof, &sources, "run.contract")
        });
        let expanded = expanded.unwrap();
        eprintln!("wide loop bundle size {size}: recheck ({work} units)");
        verify_c_sources(&expanded, &sources).unwrap();
        assert!(work > 0);
        samples.push((size, work));
    }
    // Proof shape changes can make adjacent work non-monotonic, so
    // compare the retained endpoints rather than subtracting increments.
    // At 32/64, 10/7 allows 18432*a + 128*k <= 3*B for
    // B + k*N + a*N^2. The current expansion costs about 831k and 1139k
    // units at those endpoints. The tighter bound still detects the
    // quadratic scan in the negative control below.
    let bounded = |work: &[(usize, usize)]| work[2].1 * 7 <= work[0].1 * 10;
    assert!(
        bounded(&samples),
        "wide-bundle work grew too quickly: {samples:?}"
    );
    // The old observed curve was 152088/211960/507978 at 32/64/128.
    // Forty additional units per squared member made its original guard
    // fail. Keep sensitivity to that same added quadratic scan here.
    let quadratic = samples
        .iter()
        .map(|&(size, work)| (size, work + 40 * size * size))
        .collect::<Vec<_>>();
    assert!(
        !bounded(&quadratic),
        "the smaller grid must detect the original quadratic crossover: {samples:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: arena free loop closure work regression"]
fn expanded_arena_loop_reuses_published_invariant_facts() {
    use crate::instrumentation::{VerificationEvent, collect};
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/arena/arena_cells.click");
    let (_, project, input) = crate::cli::load_sidecar_inputs(&path, None).unwrap();
    let (result, events) = collect(|| {
        crate::surface::verify_project_functions(
            &project,
            &input.program_inputs(),
            ["arena_free".to_string()],
        )
    });
    result.unwrap();
    let work: usize = events
        .iter()
        .filter_map(|event| match event {
            VerificationEvent::OperationFinished { name, work, .. }
                if name == "close invariants: members" =>
            {
                Some(*work)
            }
            _ => None,
        })
        .sum();
    // Reconstructing the already-published members cost 223,506 units;
    // checking availability first costs 174,675. Keep this outside the
    // fast gate: the small fixture there covers expansion and rejection.
    assert!(
        work > 0 && work <= 180_000,
        "redundant invariant reconstruction: {work}"
    );
}
