#[test]
fn pointer_index_fact_keys_keep_shared_dags_and_linear_work() {
    for ty in [
        MachineIntegerType::Int32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let _session = VerificationSession::enter();
            let mut root =
                KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1019020));
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
            }
            let value = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
            let fact = quantified(
                Variable(1019020),
                offset(value, 4, ty == MachineIntegerType::UInt64),
            );
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let key = proposition_identity_key(&fact).unwrap();
                assert_eq!(key, proposition_identity_key(&fact).unwrap());
                let alpha = quantified_equivalence_index_key(&fact).unwrap();
                assert_eq!(alpha, quantified_equivalence_index_key(&fact).unwrap());
            });
            assert_eq!(exports, KernelTermExport::machine_export_count());
            samples.push(work);
        }
        assert!(samples.windows(2).all(|w| w[1] <= w[0] * 5), "{samples:?}");
    }
}

#[test]
fn state_pointer_index_keys_share_growing_prefixes() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut root =
            KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1019021));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
                let value = SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap();
                let fact = fact(offset(value, 4, false));
                let key = memory_erased_proposition_key(&fact);
                assert_eq!(key, memory_erased_proposition_key(&fact));
            }
        });
        assert_eq!(exports, KernelTermExport::machine_export_count());
        samples.push(work);
    }
    assert!(samples.windows(2).all(|w| w[1] <= w[0] * 5), "{samples:?}");
}

#[test]
fn pointer_index_fact_lookup_ignores_unrelated_facts() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let make = |var, width| {
            let ty = MachineIntegerType::Int32;
            let x = KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(var));
            let root = KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [x.clone(), x]);
            quantified(
                Variable(var),
                offset(
                    SharedMachineIntegerTerm::from_shared(ty, root).unwrap(),
                    width,
                    false,
                ),
            )
        };
        let source = make(1019040, 4);
        let target = make(1019041, 4);
        let miss = make(1019041, 8);
        let unrelated: Vec<_> = (0..size)
            .map(|i| Proposition::ConditionIs(ConditionTerm::Variable(Variable(1019100 + i)), true))
            .collect();
        let parent = crate::kernel::proof::ProofFacts::from_ordered(&unrelated);
        let child = parent.with_fact(source.clone());
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(child.matching_quantified_fact(&target), Some(source));
            assert!(child.matching_quantified_fact(&miss).is_none());
            assert!(parent.matching_quantified_fact(&target).is_none());
        });
        assert_eq!(exports, KernelTermExport::machine_export_count());
        samples.push(work);
    }
    assert!(samples.windows(2).all(|w| w[1] <= w[0] * 2), "{samples:?}");
}
