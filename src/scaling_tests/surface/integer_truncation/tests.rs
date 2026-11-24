// Scaling tests of `src/surface/integer_truncation.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn integer_truncation_pure_aliases_preserve_shared_scaling() {
    let mut measured = Vec::new();
    for depth in [8, 16, 32, 64] {
        let mut source = String::from("theorem aliases(z: Integer) { let a0: Integer = z;\n");
        for index in 1..=depth {
            source.push_str(&format!("let a{index}: Integer = truncating_quotient(a{}, 3) + truncating_remainder(a{}, 3);\n", index - 1, index - 1));
        }
        source.push_str(&format!(
            "requires a{depth} == a{depth}; ensures a{depth} == a{depth} by {{ close(); }} }}"
        ));
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| verify_c_sources(&source, &[]));
        result.unwrap_or_else(|error| panic!("depth {depth}: {}", error.message()));
        measured.push(work);
    }
    for pair in measured.windows(2) {
        assert!(
            pair[1] <= 3 * pair[0],
            "truncation aliases expanded: {measured:?}"
        );
    }
}
