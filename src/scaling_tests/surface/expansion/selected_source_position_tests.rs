// Scaling tests of `src/surface/expansion.rs` (module `selected_source_position_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn one_position_does_not_convert_unrequested_tactic_positions() {
    let mut overhead = Vec::new();
    for size in [8, 32, 128] {
        let source = format!(
            "// Unicode: λ\ntheorem locations() {{ ensures 0 == 0 by {{\n close();\n // {}\n have 0 == 0 by {{ close(); }}\n close();\n}} }}\n",
            "unrelated λ ".repeat(size),
        );
        let file = parse_source_with_c_layouts(&source, &[]).unwrap();
        let (_, scan_work) = crate::instrumentation::measure_deterministic_work(|| {
            proof_source_tokens(&source, &file.source_spans().implicit_proofs).unwrap()
        });
        let (first, first_work) = crate::instrumentation::measure_deterministic_work(|| {
            tactic_source_position_file(&file, &source, "locations.ensures_0", 0).unwrap()
        });
        assert_eq!(first, SourcePosition::new(3, 2));
        overhead.push(first_work - scan_work);
        let positions =
            tactic_source_positions_file(&file, &source, "locations.ensures_0").unwrap();
        assert_eq!(positions.len(), 3);
        for (index, position) in positions.iter().enumerate() {
            assert_eq!(
                &tactic_source_position_file(&file, &source, "locations.ensures_0", index,)
                    .unwrap(),
                position,
            );
        }
        assert!(
            tactic_source_position_file(&file, &source, "locations.ensures_0", 3)
                .unwrap_err()
                .message()
                .contains("no source tactic occurrence 3")
        );
    }
    assert!(
        overhead.iter().all(|work| *work == overhead[0]),
        "converting one early location must not walk later source: {overhead:?}"
    );
}
