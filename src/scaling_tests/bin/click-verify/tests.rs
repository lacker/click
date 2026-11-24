// Scaling tests of `src/bin/click-verify.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn trace_source_locations_resolve_each_claim_once() {
    let mut cold_work = Vec::new();
    for size in [16, 64, 256] {
        let source = format!(
            "verifying \"program.c\";\nvoid sample() {{ ensures 1 == 1; }} by {{\n{}\nstep_until(function.exit); close();\n}}",
            "have 1 == 1 by { normalize(); }\n".repeat(size)
        );
        let (root, path) = temporary_project("trace-source-cache", "void sample() {}", &source);
        let target = load_target_inputs(&path, Some(&root)).unwrap();
        let locations = ProofSourceLocations::new(&target.project, &target.inputs);
        let (first, work) = click::instrumentation::measure_deterministic_work(|| {
            locations.position("sample.contract", &[0])
        });
        assert!(first.is_some());
        cold_work.push(work);
        let (_, repeated_work) = click::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                assert!(locations.position("sample.contract", &[index]).is_some());
            }
            for index in [size + 100, usize::MAX] {
                assert!(locations.position("sample.contract", &[index]).is_none());
            }
        });
        assert_eq!(locations.outer.borrow().len(), 1);
        assert_eq!(
            repeated_work, 0,
            "cached valid and missing indices must not resolve again"
        );
        fs::remove_dir_all(root).unwrap();
    }
    for pair in cold_work.windows(2) {
        assert!(
            pair[1] <= pair[0] * 5,
            "source preparation should scale linearly: {cold_work:?}"
        );
    }
}

#[test]
fn trace_source_locations_share_the_index_across_distinct_nested_sites() {
    let mut measured = Vec::new();
    for size in [16, 64, 256] {
        let source = format!(
            "verifying \"program.c\";\nvoid sample() {{ ensures 1 == 1; }} by {{\n{}\nstep_until(function.exit); close();\n}}",
            "have 1 == 1 by { normalize(); }\n".repeat(size)
        );
        let (root, path) = temporary_project("trace-nested-index", "void sample() {}", &source);
        let target = load_target_inputs(&path, Some(&root)).unwrap();
        let locations = ProofSourceLocations::new(&target.project, &target.inputs);
        locations.position("sample.contract", &[0]).unwrap();
        let tokenization = ProofSourceIndex::tokenization_work();
        let (_, work) = click::instrumentation::measure_deterministic_work(|| {
            for step in 0..size {
                let have = locations.position("sample.contract", &[step]).unwrap();
                let nested = locations.position("sample.contract", &[step, 0]).unwrap();
                assert_eq!(nested.line, step + 3);
                assert_eq!(nested.column, 18);
                assert!(
                    locations
                        .with_index(|index| index.have_body_contains(&have, &nested).unwrap())
                        .unwrap()
                );
                assert!(
                    locations
                        .with_index(|index| index.line_has_multiple_starts(&nested).unwrap())
                        .unwrap()
                );
            }
        });
        assert_eq!(
            ProofSourceIndex::tokenization_work(),
            tokenization,
            "distinct trace sites must never tokenize the source again"
        );
        assert!(
            work <= size * 4,
            "distinct nested sites must use indexed lookups: {work}"
        );
        measured.push(work);
        fs::remove_dir_all(root).unwrap();
    }
    for pair in measured.windows(2) {
        assert!(pair[1] <= pair[0] * 4, "{measured:?}");
    }
}
