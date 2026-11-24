// Scaling tests of `src/surface/tests/project_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn step_result_binding_work_scales_with_assigned_values() {
    let mut previous = None;
    for count in [8, 16, 32, 64] {
        let mut source = String::from("int32 f() {int32 x;");
        let mut proof = format!(
            "verifying \"assign.c\"; int32 f() {{ensures result=={};}} by {{step();",
            count - 1
        );
        for index in 0..count {
            source.push_str(&format!("x={index};"));
            proof.push_str(&format!("let {{ result: value_{index} }} = step();"));
        }
        source.push_str("return x;}");
        proof.push_str("have value_0==0 by {close();} step(); close();}");
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            verify_c_sources(&proof, &[("assign.c", source.as_str())])
        });
        result.unwrap();
        assert!(work > 0);
        if let Some(previous) = previous {
            assert!(
                work <= 3 * previous,
                "{count} bindings: {work} work after {previous}"
            );
        }
        previous = Some(work);
    }
}
