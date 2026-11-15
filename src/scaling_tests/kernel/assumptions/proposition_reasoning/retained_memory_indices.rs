#[test]
fn growing_state_index_comparisons_and_fingerprints_retain_dags() {
    let mut samples = vec![];
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let [before, separate, _] = reads();
        let (mut a, mut b) = (shared(&before), shared(&separate));
        let context = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                a = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [a.clone(), a],
                );
                b = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [b.clone(), b],
                );
                assert_eq!(
                    offset_state_shape(&scaled(&a)),
                    offset_state_shape(&scaled(&b))
                );
                assert!(context.operands_state_equivalent(
                    MachineOperandView::Shared(&a),
                    MachineOperandView::Shared(&b)
                ));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|p| p[1] <= 5 * p[0] + 100),
        "{samples:?}"
    );
}
