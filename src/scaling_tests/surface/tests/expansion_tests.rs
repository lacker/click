// Scaling tests of `src/surface/tests/expansion_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn selected_pure_expansion_does_not_check_unrelated_proof_bodies() {
    let selected = "theorem selected(x: int32) { ensures x == x by { normalize(); } }\n";
    expand_c_claim_source_by_label(selected, &[], "selected.ensures_0").unwrap();
    let mut samples = Vec::new();
    for size in [4, 16, 64, 256] {
        let source = format!(
            "{selected}theorem unrelated() {{ ensures 0 == 1 by {{ {} normalize(); }} }}",
            "have true by { normalize(); } ".repeat(size)
        );
        let (expanded, work) = crate::instrumentation::measure_deterministic_work(|| {
            expand_c_claim_source_by_label(&source, &[], "selected.ensures_0")
        });
        expanded.unwrap_or_else(|error| panic!("{size} unrelated steps: {error}"));
        samples.push((size, work));
    }
    eprintln!("selected pure expansion beside unrelated proof steps: {samples:?}");
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5, "{samples:?}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn partial_tactic_capture_runs_once_as_selected_sites_grow() {
    let c = [("identity.c", "int32 identity(int32 x) { return x; }")];
    let samples = [4, 8, 16, 32].map(|size| {
        let source = format!("verifying \"identity.c\";\nint32 identity(int32 x) {{ ensures result == x; }} by {{\nstep_until(function.exit);\n{}{}close();\n}}\n",
            "have x + 0 == x by close();\n".repeat(8), "have x == x by close();\n".repeat(size));
        let sites = c_smart_tactic_source_sites(&source, &c).unwrap();
        let positions = sites[9..9+size].iter().map(|s| s.position.clone()).collect::<Vec<_>>();
        let (_, ordinary_views) = proof::count_finalization_view_constructions(|| verify_c_sources(&source, &c).unwrap());
        let ((expanded, work), runs) = proof::count_finalization_view_constructions(|| {
            crate::instrumentation::measure_deterministic_work(|| expand_c_tactics_source_at(&source, &c, &positions))
        });
        let expanded = expanded.unwrap_or_else(|error| panic!("{size} selected sites: {error:?}"));
        assert_eq!(runs, ordinary_views, "{size} sites must cost one ordinary claim verification");
        assert_eq!(expanded.source.matches("have x + 0 == x by close();").count(), 8);
        verify_c_sources(&expanded.source, &c).unwrap();
        work
    });
    for pair in samples.windows(2) {
        assert!(
            pair[1] * 4 <= pair[0] * 9,
            "selected capture work grew too quickly: {samples:?}"
        );
    }
}

#[test]
fn smart_inventory_positions_are_compatible_and_scale() {
    use crate::surface::{
        c_select_smart_tactic, c_smart_tactic_source_sites, c_tactic_source_position,
    };
    let source = "// Unicode: λ\ntheorem named() { ensures 0 == 0 by { have 1 == 1 by { close(); } close(); } }\ntheorem implicit() { ensures 0 == 0; }\ntheorem short() { ensures 0 == 0 by close(); }\n";
    for site in c_smart_tactic_source_sites(source, &[]).unwrap() {
        let owner =
            c_tactic_source_position(source, &[], &site.claim_label, site.source_index).unwrap();
        assert_eq!(site.position.line, owner.line);
        assert!(site.position.column >= owner.column);
        let selected =
            c_select_smart_tactic(source, &[], site.position.line, Some(site.position.column))
                .unwrap();
        assert_eq!(selected.claim_label, site.claim_label);
        assert_eq!(selected.position, site.position);
    }
    for separate_claims in [false, true] {
        let mut measurements = Vec::new();
        for count in [8, 16, 32, 64] {
            let source = if separate_claims {
                (0..count)
                    .map(|i| format!("theorem item_{i}() {{ ensures 0 == 0 by {{ close(); }} }}\n"))
                    .collect::<String>()
            } else {
                format!(
                    "theorem item() {{ ensures 0 == 0 by {{ {} }} }}",
                    "close(); ".repeat(count)
                )
            };
            let (sites, work) = crate::instrumentation::measure_deterministic_work(|| {
                c_smart_tactic_source_sites(&source, &[]).unwrap()
            });
            assert_eq!(sites.len(), count);
            measurements.push(work);
        }
        assert!(
            measurements[3] <= 10 * measurements[0],
            "separate claims: {separate_claims}, work: {measurements:?}"
        );
    }
}
