// Scaling tests of `src/kernel/reasoning/variable_collection.rs` (module `heap_variable_projection_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn heap_variable_counts_follow_local_edits_and_keep_siblings_isolated() {
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = |id| Pointer {
            block: PointerBlock::Symbolic(Variable(id)),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut heap = crate::kernel::primitives::HeapMemory::default();
        for id in 1..=size {
            heap.uninitialized_objects.insert(pointer(id), 4);
        }
        let heap = std::sync::Arc::new(heap);
        let original = heap_variable_counts(&heap, WholeCount::Charged);
        let selected = Memory {
            heap: heap.clone(),
            ..Memory::new().with_block("selected:read", 4)
        };
        let (projected, work) = crate::instrumentation::measure_deterministic_work(|| {
            counts_whole(&selected, WholeCount::Charged)
        });
        assert_eq!(projected, original);
        assert_eq!(work, 1, "a selected read enumerated {size} heap entries");
        let mut changed = (*heap).clone();
        changed.uninitialized_objects.remove(&pointer(1));
        changed.uninitialized_objects.insert(pointer(10_000), 4);
        let changed = std::sync::Arc::new(changed);
        let (counts, work) = crate::instrumentation::measure_deterministic_work(|| {
            heap_variable_counts(&changed, WholeCount::Charged)
        });
        assert!(!counts.contains_key(&Variable(1)));
        assert!(counts.contains_key(&Variable(10_000)));
        assert_eq!(counts.len(), size as usize);
        assert!(work <= 4, "local heap edit walked {size} objects: {work}");
        assert_eq!(heap_variable_counts(&heap, WholeCount::Charged), original);
        let empty = std::sync::Arc::new(crate::kernel::primitives::HeapMemory::default());
        assert!(heap_variable_counts(&empty, WholeCount::Charged).is_empty());
        assert_eq!(heap_variable_counts(&changed, WholeCount::Charged), counts);
    }
}

#[test]
fn shared_machine_variable_bookkeeping_reuses_prefixes_in_each_collection_mode() {
    use crate::kernel::{
        KernelTerm, MachineBinaryOp, MachineIntegerType, SharedMachineIntegerTerm,
    };
    let mut samples = Vec::new();
    for size in [8usize, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = Variable(crate::kernel::ExecutionBudget::KERNEL_VARIABLE_BASE + 123);
        let format = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::Program(ProgramType::Int32), variable);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                );
                let machine = SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap();
                let condition = ConditionTerm::IntegerEqual(
                    IntegerTerm::Machine(machine.clone()).into(),
                    IntegerTerm::constant_i64(0).into(),
                );
                assert_eq!(
                    condition_syntax_execution_variable_ceiling(&condition),
                    (Some(variable), false)
                );
                let mut found = BTreeSet::new();
                assert!(!collect_condition_index_variables(&condition, &mut found));
                assert_eq!(found, BTreeSet::from([variable]));
                assert!(!machine.has_boxed_operand());
            }
        });
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small * 4 <= sw * large * 5, "{samples:?}");
    }
}

#[test]
fn shared_machine_variable_collection_keeps_state_deferral_and_load_addresses() {
    use crate::kernel::{
        KernelTerm, MachineBinaryOp, MachineIntegerType, SharedMachineIntegerTerm,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let address = Variable(crate::kernel::ExecutionBudget::KERNEL_VARIABLE_BASE + 124);
    let memory = crate::kernel::intern_memory(Memory::new());
    let load = crate::kernel::eval::load_variable_for_exact_cell(
        &memory,
        &Pointer::symbolic(address),
        crate::kernel::LoadKind::Int32,
        4,
    );
    let format = MachineIntegerType::Int32;
    let leaf = crate::kernel::eval::registered_scalar_read_term(&load, format).unwrap();
    let machine = SharedMachineIntegerTerm::from_shared(
        format,
        KernelTerm::machine_binary_shared(format, MachineBinaryOp::Add, [leaf.clone(), leaf]),
    )
    .unwrap();
    let shared = ConditionTerm::IntegerEqual(
        IntegerTerm::Machine(machine.clone()).into(),
        IntegerTerm::constant_i64(0).into(),
    );
    let written = ConditionTerm::IntegerEqual(
        IntegerTerm::from_machine(format, MachineTerm::Variable(load))
            .unwrap()
            .into(),
        IntegerTerm::constant_i64(0).into(),
    );
    let collect = |condition: &ConditionTerm| {
        let mut variables = BTreeSet::new();
        let deferred = collect_condition_index_variables(condition, &mut variables);
        (variables, deferred)
    };
    assert_eq!(collect(&shared), collect(&written));
    assert!(collect(&shared).0.contains(&address));
    assert!(collect(&shared).1);
    assert_eq!(
        condition_syntax_execution_variable_ceiling(&shared),
        condition_syntax_execution_variable_ceiling(&written)
    );
    assert!(!machine.has_boxed_operand());
    crate::kernel::eval::clear_load_variable_registry();
    assert_eq!(collect(&shared), (BTreeSet::from([address]), true));
    assert!(!machine.has_boxed_operand());
}
