// Scaling tests of `src/kernel/primitives/memory_construction_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn construction_recording_cost_is_independent_of_state_size() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut costs = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut memory = Memory::new();
        for i in 0..size {
            memory = memory.store(
                Pointer {
                    block: "local:scale".into(),
                    offset: PointerOffsetTerm::Constant(i * 4),
                },
                ProgramValue::Int32((i as u32).into()),
            );
        }
        let (_, cost) = crate::instrumentation::measure_deterministic_work(|| {
            memory.record_diagnostic_transform("diagnostic test", vec![Memory::new()], Vec::new());
        });
        costs.push(cost);
    }
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}
