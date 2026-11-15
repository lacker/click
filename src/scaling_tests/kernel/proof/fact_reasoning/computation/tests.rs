// Goal-local computational refusal must not traverse the selected snapshots.
use super::*;

#[test]
fn computation_refusal_is_independent_of_memory_history() {
    let mut costs = Vec::new();
    for size in [4, 16, 64, 256] {
        let _session = VerificationSession::enter();
        let pointer = Pointer {
            block: PointerBlock::Concrete("computation-read".into()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let other = Pointer {
            block: PointerBlock::Concrete("computation-write".into()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = crate::kernel::intern_memory(
            Memory::new()
                .with_block("computation-read", 4)
                .with_block("computation-write", 4),
        );
        let mut after = before.memory().clone();
        for _ in 0..size {
            after = after.store(other.clone(), ProgramValue::Int32(MachineTerm::constant(7)));
        }
        let after = crate::kernel::intern_memory(after);
        let left =
            MachineTerm::MemoryLoad(before.clone(), Box::new(pointer.clone()), LoadKind::Int32);
        let right = MachineTerm::MemoryLoad(after, Box::new(pointer.clone()), LoadKind::Int32);
        let read_equality =
            Proposition::ConditionIs(ConditionTerm::equal(left.clone(), right), true);
        let add = |left, right| MachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op: MachineBinaryOp::Add,
            left: Box::new(left),
            right: Box::new(right),
        };
        let rearranged = Proposition::ConditionIs(
            ConditionTerm::equal(
                add(left.clone(), MachineTerm::constant(1)),
                add(MachineTerm::constant(1), left),
            ),
            true,
        );
        let ((resolved, cancelled), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                (computes_leaf(&read_equality), computes_leaf(&rearranged))
            });
        assert!(!resolved);
        assert!(cancelled);
        costs.push(work);
        assert!(computes_leaf(&Proposition::MemoryLoadable {
            memory: before.memory().clone(),
            base: pointer,
            bytes: MachineTerm::constant(4),
            wide: false,
        }));
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work == costs[0]),
        "{costs:?}"
    );
}

#[test]
fn direct_validity_queries_ignore_cells_and_store_history() {
    for related in [false, true] {
        let mut samples = Vec::new();
        for size in [4, 16, 64, 256] {
            let _session = VerificationSession::enter();
            let pointer = Pointer {
                block: PointerBlock::Concrete("direct-read".into()),
                offset: PointerOffsetTerm::Constant(0),
            };
            let other = Pointer {
                block: PointerBlock::Concrete("direct-other".into()),
                offset: PointerOffsetTerm::Constant(0),
            };
            let mut memory = Memory::new()
                .with_block("direct-read", 4)
                .with_block("direct-other", 4096)
                .store(
                    pointer.clone(),
                    ProgramValue::UInt32(MachineTerm::uint32_constant(7)),
                );
            for index in 0..size {
                let target = if related {
                    pointer.clone()
                } else {
                    other.offset_by_bytes(index * 4)
                };
                memory = memory.store(
                    target,
                    ProgramValue::UInt32(MachineTerm::uint32_constant(7)),
                );
            }
            let hit = Proposition::MemoryReadDefined {
                memory: memory.clone(),
                pointer: pointer.clone(),
                value_type: ProgramType::UInt32,
            };
            let miss = Proposition::MemoryReadDefined {
                memory: memory.clone(),
                pointer: pointer.offset_by_bytes(3),
                value_type: ProgramType::UInt32,
            };
            let bounds = Proposition::MemoryLoadable {
                memory,
                base: pointer,
                bytes: MachineTerm::constant(4),
                wide: false,
            };
            let ((hit, miss, bounds), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    (
                        computes_leaf(&hit),
                        computes_leaf(&miss),
                        computes_leaf(&bounds),
                    )
                });
            assert!(hit && !miss && bounds);
            samples.push(work);
        }
        assert!(
            samples[0] > 0 && samples.iter().all(|work| *work == samples[0]),
            "{samples:?}"
        );
    }
}

#[test]
fn intrinsic_bounds_visit_shared_machine_nodes_once_without_exporting() {
    use num_bigint::BigInt;
    let mut samples = Vec::new();
    for depth in [4usize, 8, 16, 32] {
        let _session = VerificationSession::enter();
        let mut import = KernelTermImport::default();
        let format = MachineIntegerType::UInt64;
        let mut root = KernelTerm::machine_if_shared(
            format,
            [
                KernelTerm::variable(KernelType::Bool, Variable(918_000)),
                import.machine(format, &MachineTerm::uint64_constant(0)),
                import.machine(format, &MachineTerm::uint64_constant(1)),
            ],
        );
        for _ in 0..depth {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let observation = SharedMachineIntegerTerm::from_shared(format, root).unwrap();
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(
                IntegerTerm::Machine(observation.clone()).into(),
                IntegerTerm::constant(BigInt::from(1u8) << depth).into(),
            ),
            true,
        );
        assert!(!observation.has_boxed_operand());
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| computes_leaf(&goal));
        assert!(result);
        assert!(!observation.has_boxed_operand());
        samples.push(work);
    }
    assert!(
        samples[0] > 0 && samples.windows(2).all(|pair| pair[1] <= pair[0] * 3),
        "{samples:?}"
    );
}

#[test]
fn direct_validity_refuses_retired_storage_and_incomplete_pointer_bytes() {
    let _session = VerificationSession::enter();
    let pointer = Pointer {
        block: PointerBlock::Concrete("retired".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut memory = Memory::new().with_block("retired", 8);
    for offset in 0..8 {
        memory = memory.store(pointer.offset_by_bytes(offset), crate::kernel::uint8(0));
    }
    let defined = |memory, value_type| Proposition::MemoryReadDefined {
        memory,
        pointer: pointer.clone(),
        value_type,
    };
    assert!(computes_leaf(&defined(memory.clone(), ProgramType::UInt64)));
    assert!(!computes_leaf(&defined(
        memory.clone(),
        ProgramType::VoidPointer
    )));
    let retired = memory.without_local_block(&pointer.block);
    assert!(!computes_leaf(&defined(
        retired.clone(),
        ProgramType::UInt64
    )));
    assert!(!computes_leaf(&Proposition::MemoryLoadable {
        memory: retired,
        base: pointer,
        bytes: MachineTerm::constant(8),
        wide: false
    }));
}
