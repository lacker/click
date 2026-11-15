// Scaling tests of `src/kernel/reasoning/memory_resolution.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[cfg(test)]
#[test]
fn memory_resolution_graph_offset_queries_scale_without_legacy_fact_index() {
    for size in [16u64, 64, 256, 512] {
        let scalar = |id| MachineTerm::Variable(Variable(92_000 + id));
        let offset = |id| PointerOffsetTerm::scale_int32(scalar(id), 4);
        let named = PointerOffsetTerm::Variable(Variable(94_000));
        let mut context = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_offset_equal(offset(0), named.clone()),
            true,
        );
        for index in 0..size {
            context = context
                .assume_condition(ConditionTerm::equal(scalar(index), scalar(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                assert_eq!(
                    pointer_offsets_equal_for_memory_resolution(&offset(index), &named, &context),
                    Some(true)
                );
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 200 * size as usize, "size={size}, work={work}");
    }
}

#[cfg(test)]
#[test]
fn stored_load_alias_lookup_ignores_unrelated_cells() {
    let target = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(8_991_001)), 4),
    };
    let alias = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(8_991_002)), 4),
    };
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_offset_equal(target.offset.clone(), alias.offset.clone()),
        true,
    );
    let mut samples = Vec::new();
    for count in [8, 32, 128, 512] {
        let mut memory = Memory::new();
        for index in 0..count {
            memory = memory.store(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::Constant(index * 4),
                },
                ProgramValue::Int32(MachineTerm::constant(0)),
            );
        }
        // Memory state construction/interning belongs to the producer. Measure
        // only a lookup in the already established state.
        crate::kernel::intern_memory_ref(&memory);
        let (absent, work) = crate::instrumentation::measure_deterministic_work(|| {
            stored_value_at_equal_pointer(&memory, &target, &assumptions)
        });
        assert!(absent.is_none());
        samples.push(work);
        let value = ProgramValue::Int32(MachineTerm::constant(17));
        memory = memory.store(alias.clone(), value.clone());
        assert_eq!(
            stored_value_at_equal_pointer(&memory, &target, &assumptions),
            Some(value)
        );
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 16),
        "{samples:?}"
    );
}

#[cfg(test)]
#[test]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn interior_base_alias_frames_only_distinct_objects_and_is_indexed() {
    let base = Pointer {
        block: PointerBlock::Heap(920_000),
        offset: PointerOffsetTerm::Constant(0),
    };
    let alias = Pointer {
        block: PointerBlock::Symbolic(Variable(920_001)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let local = Pointer {
        block: "local:interior-alias-store".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let equality = ConditionTerm::pointer_equal(alias.clone(), base.clone());
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut facts = PureFactContext::new();
        for index in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer {
                        block: PointerBlock::Symbolic(Variable(930_000 + index)),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    Pointer {
                        block: PointerBlock::Heap(940_000 + index),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                ),
                true,
            );
        }
        let absent = facts.clone();
        facts = facts.assume_condition(equality.clone(), true);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for offset in [-1i64, 0, 1, 2, 3, 16] {
                let read = Pointer {
                    offset: PointerOffsetTerm::Constant(offset),
                    ..alias.clone()
                };
                assert!(pointers_proven_distinct_for_memory_resolution(
                    &local, &read, &facts
                ));
                assert!(
                    crate::kernel::memory_provenance::write_access_is_disjoint_from_load(
                        &local, 4, &read, 4, &facts
                    )
                );
            }
        });
        samples.push((size, work));
        let interior = Pointer {
            offset: PointerOffsetTerm::Constant(1),
            ..alias.clone()
        };
        assert!(!pointers_proven_distinct_for_memory_resolution(
            &local, &interior, &absent
        ));
        // Different starting addresses in the same object are insufficient
        // evidence for either an exact interior alias or a multi-byte frame.
        assert!(!pointers_proven_distinct_for_memory_resolution(
            &base, &interior, &facts
        ));
        assert!(
            !crate::kernel::memory_provenance::write_access_is_disjoint_from_load(
                &base, 4, &interior, 4, &facts
            )
        );
    }
    eprintln!("interior alias frame (N, units): {samples:?}");
    let baseline = samples[0].1;
    assert!(
        samples.iter().all(|(_, work)| *work <= baseline + 256),
        "interior alias framing scanned unrelated facts: {samples:?}"
    );
}

#[cfg(test)]
#[test]
fn mixed_index_offsets_work_ignores_unrelated_facts() {
    use crate::kernel::{IntegerTerm, MachineIntegerType};
    let wide = MachineTerm::Variable(Variable(82001));
    let narrow = MachineTerm::Variable(Variable(82002));
    let native = PointerOffsetTerm::scale_int64(wide.clone(), 1, true);
    let signed = PointerOffsetTerm::scale_int32(narrow.clone(), 1);
    let fact = ConditionTerm::IntegerEqual(
        IntegerTerm::from_machine(MachineIntegerType::UInt64, wide)
            .unwrap()
            .into(),
        IntegerTerm::from_machine(MachineIntegerType::Int32, narrow)
            .unwrap()
            .into(),
    );
    let mut counts = Vec::new();
    for size in [8, 32, 128] {
        let mut context = PureFactContext::new().assume_condition(fact.clone(), true);
        for i in 0..size {
            context = context.assume_condition(
                ConditionTerm::IntegerEqual(
                    IntegerTerm::Variable(Variable(83000 + i)).into(),
                    IntegerTerm::constant_i64(i as i64).into(),
                ),
                true,
            );
        }
        let (answer, units) = crate::instrumentation::measure_deterministic_work(|| {
            mixed_index_offsets_equal(&native, &signed, &context)
        });
        assert_eq!(answer, Some(true));
        counts.push(units);
    }
    assert_eq!(counts[0], counts[1]);
    assert_eq!(counts[1], counts[2]);
    assert!(counts[0] > 0);
}

/// A load through an unresolved pointer observes every pointer-reachable
/// cell, so its canonical memory keeps the cells of every other object; it is
/// projected from the store's maintained reachable map rather than rebuilt
/// cell by cell, and the slots of locals no pointer reaches are not visited
/// (`roadmap/scaling.md` cause 6). Canonicalizing the newest object's load
/// along one memory lineage costs the same beside 16, 64 or 256 earlier
/// objects and hidden slots.
#[test]
fn unresolved_load_projection_ignores_earlier_objects_and_hidden_slots() {
    let mut samples = Vec::new();
    for size in [16usize, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        crate::kernel::set_never_address_taken_locals(
            (0..=size).map(|index| format!("hidden{index}")).collect(),
        );
        let slot = |index: usize| Pointer {
            block: PointerBlock::Concrete(format!("local:hidden{index}")),
            offset: PointerOffsetTerm::Constant(0),
        };
        let object = |index: usize| Pointer::symbolic(Variable(98_700 + index as u64));
        let value = |index: usize| ProgramValue::Int32((index as u32).into());
        let mut memory = Memory::new();
        let mut last = 0;
        for index in 0..=size {
            memory = memory
                .with_block(slot(index).block.clone(), 4)
                .store(slot(index), value(index))
                .store(object(index), value(index));
            let (canonical, work) = crate::instrumentation::measure_deterministic_work(|| {
                canonical_memory_for_pointer_load(&memory, &object(index))
            });
            if index == size {
                assert!(
                    index == 0 || canonical.has_known_cell_at(&object(index - 1)),
                    "size {size}: the projection dropped another object's cell"
                );
                assert!(
                    !canonical.has_known_cell_at(&slot(0)),
                    "size {size}: the projection kept a slot no pointer reaches"
                );
                last = work;
            }
        }
        crate::kernel::clear_never_address_taken_locals();
        samples.push((size, last));
    }
    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 4),
        "an unresolved load's projection grows with earlier objects: {samples:?}"
    );
}

#[test]
fn retained_endpoint_queries_reuse_shared_dag_pairs() {
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelType, MachineIntegerType as T, MachineOperandView as V,
    };
    let samples = [8usize, 32, 128].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let mut root = KernelTerm::variable(
            KernelType::Program(T::Int32.program_type()),
            Variable(993891),
        );
        let other = KernelTerm::variable(
            KernelType::Program(T::Int32.program_type()),
            Variable(993892),
        );
        let context = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    T::Int32,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                );
                assert!(!int32_operand_values_equal_for_memory_resolution(
                    V::Shared(&root),
                    V::Shared(&other),
                    &context
                ));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        (size, work)
    });
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}

#[test]
fn run_access_retains_cold_shared_index_dags() {
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, MachineOperandView,
    };
    for ty in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut term =
                KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1018601));
            for _ in 0..size {
                term = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [term.clone(), term],
                );
            }
            let retained = MachineOperandView::Shared(&term).retain(ty);
            let base = Pointer {
                block: "retained_run".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let run = CellRun::new(
                base.clone(),
                4,
                ProgramType::Int32,
                16,
                crate::kernel::intern_memory(Memory::new()),
                Default::default(),
            );
            let offset = if ty == MachineIntegerType::Int32 {
                PointerOffsetTerm::Int32Scaled {
                    value: retained.clone(),
                    byte_width: 4,
                }
            } else {
                PointerOffsetTerm::Int64Scaled {
                    value: retained.clone(),
                    byte_width: 4,
                    unsigned: true,
                }
            };
            let pointer = Pointer {
                block: base.block,
                offset,
            };
            let exports = KernelTermExport::machine_export_count();
            let (access, work) =
                crate::instrumentation::measure_deterministic_work(|| run_access(&run, &pointer));
            match access {
                RunAccess::Scaled {
                    index,
                    scale,
                    shift,
                }
                | RunAccess::ScaledWide {
                    index,
                    scale,
                    shift,
                } => {
                    assert_eq!(index, retained);
                    assert_eq!((scale, shift), (4, 0));
                }
                other => panic!("unexpected access: {other:?}"),
            }
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            samples.push((size, work));
        }
        for (size, work) in &samples {
            assert!(*work <= 32 * size + 32, "{ty:?}: {samples:?}");
        }
    }
}

#[test]
fn wide_offset_step_retains_dags_and_ignores_unrelated_facts() {
    use crate::kernel::assumptions::{wide_index_binary, wide_index_comparison};
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, MachineOperandView,
    };
    let ty = MachineIntegerType::UInt64;
    for size in [16, 64, 256] {
        let mut samples = Vec::new();
        for unrelated in [0, size] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut root =
                KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1018703));
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
            }
            let index = MachineOperandView::Shared(&root).retain(ty);
            let advanced = wide_index_binary(
                MachineBinaryOp::Add,
                index.operand_view(),
                MachineOperandView::Legacy(&MachineTerm::uint64_constant(1)),
            );
            let scaled = |value| PointerOffsetTerm::Int64Scaled {
                value,
                byte_width: 8,
                unsigned: true,
            };
            let stepped = PointerOffsetTerm::Add(
                Box::new(scaled(index.clone())),
                Box::new(PointerOffsetTerm::Constant(8)),
            );
            let whole = scaled(advanced);
            let mut facts = PureFactContext::new().assume_condition(
                wide_index_comparison(
                    CompareRelation::LessEqual,
                    index.operand_view(),
                    MachineOperandView::Legacy(&MachineTerm::uint64_constant(u64::MAX - 1)),
                ),
                true,
            );
            for extra in 0..unrelated {
                facts = facts.assume_condition(
                    ConditionTerm::equal(
                        MachineTerm::Variable(Variable(1019000 + extra as u64)),
                        MachineTerm::constant(3),
                    ),
                    true,
                );
            }
            let _scope = facts.enter_id_scope();
            let exports = KernelTermExport::machine_export_count();
            let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
                pointer_offsets_equal_for_memory_resolution(&stepped, &whole, &facts)
            });
            assert_eq!(answer, Some(true));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(
                work <= 128 * size + 256,
                "size={size}, unrelated={unrelated}, work={work}"
            );
            samples.push(work);
        }
        assert!(
            samples[1] <= 2 * samples[0] + 32,
            "size={size}: {samples:?}"
        );
    }
}

/// Reading a byte product as its element index is one overflow decision on
/// the product's own operands: the comparison's work does not grow as
/// unrelated bounded indices and their facts grow.
#[cfg(test)]
#[test]
fn a_byte_product_comparison_ignores_unrelated_bounded_indices() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 512] {
        let scalar = |id| MachineTerm::Variable(Variable(96_000 + id));
        let bounds = |context: PureFactContext, id| {
            context
                .assume_condition(
                    ConditionTerm::signed_less_equal(MachineTerm::constant(0), scalar(id)),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_than(scalar(id), MachineTerm::constant(4)),
                    true,
                )
        };
        let mut context = bounds(PureFactContext::new(), 0);
        for id in 1..=size {
            context = bounds(context, id);
        }
        let bytes = PointerOffsetTerm::scale_int32(
            MachineTerm::multiply(scalar(0), MachineTerm::constant(4)),
            1,
        );
        let elements = PointerOffsetTerm::scale_int32(scalar(0), 4);
        let _scope = context.enter_id_scope();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                pointer_offsets_equal_for_memory_resolution(&bytes, &elements, &context),
                Some(true)
            );
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "unrelated indices changed the comparison's work: {samples:?}"
    );
}
