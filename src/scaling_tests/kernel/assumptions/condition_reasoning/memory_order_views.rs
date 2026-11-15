#[test]
fn memory_order_queries_scale_across_growing_prefixes_and_fact_contexts() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(993211));
        let target =
            IntegerTerm::from_machine(format, MachineTerm::Variable(Variable(993212))).unwrap();
        let mut facts = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                facts = facts.assume_condition(
                    ConditionTerm::signed_less_equal(
                        0u32.into(),
                        MachineTerm::Variable(Variable(994000 + index)),
                    ),
                    true,
                );
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Multiply,
                    [root.clone(), root.clone()],
                );
                let query = ConditionTerm::integer_less_than(
                    IntegerTerm::Machine(
                        SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap(),
                    ),
                    target.clone(),
                );
                assert!(!facts.proves_order_condition_for_memory_resolution(&query, true));
                let child = facts.clone().assume_condition(query.clone(), true);
                assert!(
                    child.proves_order_condition_for_memory_resolution(&query, true),
                    "size {size}, prefix {index}: exact {:?}, graph {}",
                    child.exact_condition_value(&query),
                    child.difference_graph_proves(&query)
                );
                assert!(!facts.proves_order_condition_for_memory_resolution(&query, true));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5, "{samples:?}");
    }
}

#[test]
fn shared_read_order_bucket_ignores_unrelated_addresses() {
    let mut samples = Vec::new();
    for unrelated in [0usize, 32, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::symbolic(Variable(993_221));
        let mut context = PureFactContext::new();
        for index in 0..(unrelated + 8) {
            let address = if index < 8 {
                pointer.clone()
            } else {
                Pointer::symbolic(Variable(993_300 + index as u64))
            };
            let memory = crate::kernel::intern_memory(
                Memory::new().with_block(format!("order-retained_state-{index}"), 0),
            );
            let read = MachineTerm::MemoryLoad(memory, Box::new(address), LoadKind::Int32);
            let shared = KernelTermImport::default()
                .machine_arithmetic(MachineIntegerType::Int32, &read)
                .unwrap();
            let upper = MachineTerm::constant(20);
            let condition = crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::Int32,
                CompareRelation::LessThan,
                [
                    MachineOperandView::Shared(&shared),
                    MachineOperandView::Legacy(&upper),
                ],
            );
            context = context.assume_condition(condition, true);
        }
        let (count, work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .order_facts_by_lower
                .loads_of(&pointer, LoadKind::Int32)
                .count()
        });
        assert_eq!(count, 8);
        samples.push(work);
    }
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn aligned_shared_sums_check_selected_read_authority_in_linear_work() {
    fn sample(size: usize, unrelated: usize) -> usize {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let write_index = MachineTerm::Variable(Variable(996_001));
        let base = Pointer {
            block: "framed-sums".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let pointers: Vec<_> = (0..size)
            .map(|index| {
                base.offset_by_elements(MachineTerm::Variable(Variable(996_100 + index as u64)), 4)
            })
            .collect();
        let mut context = PureFactContext::new();
        for index in 0..unrelated {
            context = context.assume_proposition(Proposition::Predicate {
                name: format!("unrelated_sum_fact_{index}"),
                arguments: vec![],
            });
        }
        let weak = context.clone();
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::signed_less_than(
                    MachineTerm::Variable(Variable(996_100 + index as u64)),
                    write_index.clone(),
                ),
                true,
            );
        }
        let before = Memory::new().with_block("framed-sums", 1024);
        let after = before.clone().store_with_context(
            base.offset_by_elements(write_index, 4),
            ProgramValue::Int32(MachineTerm::constant(9)),
            &context,
        );
        let before = crate::kernel::intern_memory(before);
        let after = crate::kernel::intern_memory(after);
        let zero = KernelTermImport::default()
            .machine_arithmetic(format, &MachineTerm::constant(0))
            .unwrap();
        let (mut left, mut right) = (zero.clone(), zero);
        for pointer in pointers {
            crate::kernel::eval::declare_load_access_width(&pointer, 4);
            let read = |memory: &SharedMemory| {
                let name = crate::kernel::eval::load_variable_for_exact_cell(
                    memory,
                    &pointer,
                    LoadKind::Int32,
                    4,
                );
                KernelTermImport::default()
                    .machine_arithmetic(format, &MachineTerm::Variable(name))
                    .unwrap()
            };
            left = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [left, read(&before)],
            );
            right = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [right, read(&after)],
            );
        }
        let views = || {
            (
                MachineOperandView::Shared(&left),
                MachineOperandView::Shared(&right),
            )
        };
        let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
            let (left, right) = views();
            context.word_addends_equal_views(left, right)
        });
        assert!(proved);
        // Shared syntax may be warm, but a successful frame decision in one
        // context must not become authority in another context.
        let (left, right) = views();
        assert!(!weak.word_addends_equal_views(left, right));
        assert!(context.word_addends_equal_views(left, right));
        work
    }
    let growth = [8, 16, 32, 64].map(|size| sample(size, 32));
    assert!(growth[0] > 0);
    for pair in growth.windows(2) {
        assert!(pair[1] <= 3 * pair[0], "selected read growth: {growth:?}");
    }
    let ambient = [0, 32, 128, 512].map(|unrelated| sample(8, unrelated));
    assert!(
        ambient.iter().all(|work| *work == ambient[0]),
        "unrelated facts: {ambient:?}"
    );
}
