use super::*;
use crate::kernel::{MachineCastSpelling, MachineTerm};

#[test]
fn shared_term_bridges_visit_nodes_once_beside_unrelated_terms() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(900_000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 32, 64, 128] {
            let mut source: SharedIntegerTerm = IntegerTerm::Variable(Variable(901_000)).into();
            for _ in 0..size {
                source = IntegerTerm::Add(source.clone(), source).into();
            }
            let ((imported, restored), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let imported = KernelTermImport::default().integer(&source);
                    let restored = KernelTermExport::default().integer(&imported).unwrap();
                    (imported, restored)
                });
            assert_eq!(restored, source);
            assert_eq!(imported.ty(), &KernelType::Integer);
            assert!(
                work <= 12 * (size + 1),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn machine_term_bridge_is_linear_in_explicit_tree_size() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(920_000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut bits = MachineTerm::Variable(Variable(921_000));
            for i in 0..size {
                bits = MachineTerm::Binary {
                    format: MachineIntegerType::Int32,
                    op: match i % 3 {
                        0 => MachineBinaryOp::Add,
                        1 => MachineBinaryOp::ShiftLeft,
                        _ => MachineBinaryOp::ShiftRight,
                    },
                    left: Box::new(bits),
                    right: Box::new(MachineTerm::constant(1)),
                };
            }
            let source = PureFunctionArgument::Value(ProgramValue::Int32(bits));
            let (restored, work) = crate::instrumentation::measure_deterministic_work(|| {
                let term = KernelTermImport::default().argument(&source);
                KernelTermExport::default().argument(&term).unwrap()
            });
            assert_eq!(restored, source);
            assert!(
                work <= 8 * (size + 1),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn specialized_cast_bridge_is_linear_beside_unrelated_terms() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(930_000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut bits = MachineTerm::Variable(Variable(931_000));
            for _ in 0..size {
                bits = MachineTerm::legacy_cast(
                    MachineCastSpelling::UInt32From64,
                    Box::new(MachineTerm::legacy_cast(
                        MachineCastSpelling::UInt64From32,
                        Box::new(bits),
                    )),
                );
            }
            let source = PureFunctionArgument::Value(ProgramValue::UInt32(bits));
            let (restored, work) = crate::instrumentation::measure_deterministic_work(|| {
                let term = KernelTermImport::default().argument(&source);
                KernelTermExport::default().argument(&term).unwrap()
            });
            assert_eq!(restored, source);
            // Two unary casts per level, one leaf; import, intern and export
            // each charge constant work per explicit node.
            assert!(
                work <= 8 * (2 * size + 1),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn machine_observation_bridge_scales_with_its_explicit_operand() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(940_000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut bits = MachineTerm::Variable(Variable(941_000));
            for _ in 0..size {
                bits = MachineTerm::Binary {
                    format: MachineIntegerType::Int32,
                    op: MachineBinaryOp::Add,
                    left: Box::new(bits),
                    right: Box::new(MachineTerm::constant(1)),
                };
            }
            let machine = SharedMachineIntegerTerm::intern(MachineIntegerType::Int32, bits);
            let source: SharedIntegerTerm = IntegerTerm::Machine(machine.clone()).into();
            let (restored, work) = crate::instrumentation::measure_deterministic_work(|| {
                let term = KernelTermImport::default().integer(&source);
                drop(source);
                KernelTermExport::default().integer(&term).unwrap()
            });
            assert!(
                matches!(restored.as_ref(), IntegerTerm::Machine(actual) if actual.id() == machine.id())
            );
            assert!(
                work <= 8 * (size + 2),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn integer_conversion_bridge_scales_with_shared_operand() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(950_000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut value: SharedIntegerTerm = IntegerTerm::Variable(Variable(951_000)).into();
            for _ in 0..size {
                value = IntegerTerm::Add(value.clone(), value).into();
            }
            let source =
                PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::IntegerToMachine {
                    value,
                    destination: MachineIntegerType::Int32,
                }));
            let (restored, work) = crate::instrumentation::measure_deterministic_work(|| {
                let term = KernelTermImport::default().argument(&source);
                KernelTermExport::default().argument(&term).unwrap()
            });
            assert_eq!(restored, source);
            assert!(
                work <= 12 * (size + 2),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn boolean_conversion_bridge_is_linear_in_explicit_conditions() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(962_000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut condition = ConditionTerm::Variable(Variable(963_000));
            for _ in 0..size {
                condition = ConditionTerm::BoolIf {
                    condition: Box::new(ConditionTerm::Variable(Variable(963_001))),
                    then_condition: Box::new(condition),
                    else_condition: Box::new(ConditionTerm::Constant(false)),
                };
            }
            let source = PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::BoolCast {
                to: MachineIntegerType::Int32,
                value: Box::new(condition),
            }));
            let (restored, work) = crate::instrumentation::measure_deterministic_work(|| {
                let term = KernelTermImport::default().argument(&source);
                KernelTermExport::default().argument(&term).unwrap()
            });
            assert_eq!(restored, source);
            assert!(
                work <= 24 * (size + 2),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn integer_comparison_bridge_reconstructs_shared_operands_linearly() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(965_000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut value: SharedIntegerTerm = IntegerTerm::Variable(Variable(966_000)).into();
            for _ in 0..size {
                value = IntegerTerm::Add(value.clone(), value).into();
            }
            let source = ConditionTerm::IntegerGreaterEqual(value.clone(), value);
            let ((term, restored), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let term = KernelTermImport::default().condition(&source);
                    drop(source);
                    let restored = KernelTermExport::condition(&term).unwrap();
                    (term, restored)
                });
            assert_eq!(KernelTermImport::default().condition(&restored), term);
            assert!(
                work <= 24 * (size + 2),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn observing_every_shared_machine_prefix_does_not_materialize_operands() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(951000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let format = MachineIntegerType::Int64;
            let mut term =
                KernelTerm::variable(KernelType::Program(ProgramType::Int64), Variable(952000));
            let mut retained = Vec::new();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    // The boxed expansion would double at every level. Both
                    // observation construction and its Integer bridge must
                    // retain handles, including after bridge memo reset.
                    term = KernelTerm::arithmetic_binary(
                        format,
                        MachineBinaryOp::Add,
                        [term.clone(), term.clone()],
                    )
                    .unwrap();
                    let observation =
                        SharedMachineIntegerTerm::from_shared(format, term.clone()).unwrap();
                    let source: SharedIntegerTerm =
                        IntegerTerm::Machine(observation.clone()).into();
                    let common = KernelTermImport::default().integer(&source);
                    drop(source);
                    clear_integer_bridge_memo();
                    let restored = KernelTermExport::default().integer(&common).unwrap();
                    let IntegerTerm::Machine(actual) = restored.as_ref() else {
                        panic!("machine observation");
                    };
                    assert_eq!(actual.id(), observation.id());
                    assert!(actual.value_reading().is_none());
                    assert!(!actual.has_boxed_operand());
                    retained.push(restored);
                }
            });
            assert!(
                work <= 20 * size,
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn machine_root_checking_views_keep_shared_prefixes_unboxed() {
    let mut baseline = Vec::new();
    for unrelated in [0, 128, 512] {
        let mut costs = Vec::new();
        let _ambient = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(955000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let format = MachineIntegerType::Int64;
            let mut term =
                KernelTerm::variable(KernelType::Program(ProgramType::Int64), Variable(956000));
            let mut retained = Vec::new();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    term = KernelTerm::arithmetic_binary(
                        format,
                        MachineBinaryOp::Add,
                        [term.clone(), term.clone()],
                    )
                    .unwrap();
                    let observation =
                        SharedMachineIntegerTerm::from_shared(format, term.clone()).unwrap();
                    let source = IntegerTerm::Machine(observation.clone());
                    let exact =
                        crate::kernel::machine_integer::identity::mathematical(&source).unwrap();
                    assert_eq!(exact.0, format);
                    assert_eq!(
                        crate::kernel::machine_integer::identity::additive_mathematical(&source),
                        Some(exact)
                    );
                    assert!(
                        crate::kernel::machine_integer::bounds::operation_bound(&observation, true)
                            .is_none()
                    );
                    let range =
                        crate::kernel::machine_integer::range::range_fact(&observation, true);
                    assert!(
                        crate::kernel::proof::integer_arithmetic::integer_affine_claim(&range)
                            .is_some()
                    );
                    let quotient = KernelTerm::intern(
                        KernelType::Program(format.program_type()),
                        KernelTermNode::MachineBinary {
                            format,
                            operator: MachineBinaryOp::Divide,
                            arguments: [
                                term.clone(),
                                KernelTermImport::default()
                                    .machine(format, &MachineTerm::int64_constant(2)),
                            ],
                        },
                    );
                    let quotient = SharedMachineIntegerTerm::from_shared(format, quotient).unwrap();
                    for upper in [false, true] {
                        assert!(
                            crate::kernel::machine_integer::bounds::operation_bound(
                                &quotient, upper
                            )
                            .is_some()
                        );
                    }
                    assert!(!quotient.has_boxed_operand());
                    assert!(!observation.has_boxed_operand());
                    retained.push(source);
                }
            });
            costs.push((size, work));
        }
        for pair in costs.windows(2) {
            let [(small, small_work), (large, large_work)] = pair else {
                unreachable!()
            };
            assert!(
                large_work * small * 4 <= small_work * large * 5,
                "{costs:?}"
            );
        }
        if unrelated == 0 {
            baseline = costs;
        } else {
            assert_eq!(
                costs, baseline,
                "unrelated terms must not add checking work"
            );
        }
    }
}

#[test]
fn retained_load_terms_grow_without_rewalking_states_or_prior_arithmetic() {
    for unrelated in [0, 128, 512] {
        let mut memory = Memory::new();
        for index in 0..unrelated {
            memory = memory.with_block(format!("unrelated-read-{index}"), 4);
        }
        let memory = intern_memory(memory);
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let mut root =
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(993200));
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for index in 0..size {
                    let read = MachineTerm::MemoryLoad(
                        memory.clone(),
                        Box::new(Pointer::symbolic(Variable(993201 + index))),
                        LoadKind::Int32,
                    );
                    let leaf =
                        KernelTermImport::default().machine(MachineIntegerType::Int32, &read);
                    assert!(matches!(leaf.node(), KernelTermNode::MemoryLoad { .. }));
                    root = KernelTerm::arithmetic_binary(
                        MachineIntegerType::Int32,
                        MachineBinaryOp::Add,
                        [root.clone(), leaf],
                    )
                    .unwrap();
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(
                work <= 8 * size as usize,
                "size={size} unrelated={unrelated} work={work}"
            );
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 5, "{samples:?}");
        }
    }
}

#[test]
fn retained_named_reads_do_not_rewalk_their_address_on_each_import() {
    let _session = crate::kernel::VerificationSession::enter();
    for size in [16, 64, 256] {
        let mut offset = PointerOffsetTerm::Variable(Variable(993500));
        for index in 0..size {
            offset = PointerOffsetTerm::Add(
                Box::new(offset),
                Box::new(PointerOffsetTerm::Variable(Variable(993501 + index))),
            );
        }
        let raw = MachineTerm::MemoryLoad(
            intern_memory(Memory::new()),
            Box::new(Pointer {
                block: PointerBlock::Symbolic(Variable(993499)),
                offset,
            }),
            LoadKind::Int32,
        );
        let (name, _) = crate::kernel::eval::load_variable_for_term(&raw).unwrap();
        let expected =
            crate::kernel::eval::registered_scalar_read_term(&name, MachineIntegerType::Int32)
                .unwrap();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                assert_eq!(
                    crate::kernel::eval::registered_scalar_read_term(
                        &name,
                        MachineIntegerType::Int32
                    )
                    .unwrap(),
                    expected,
                );
            }
        });
        assert!(work <= 3 * size as usize, "size={size} work={work}");
    }
}

#[test]
fn shared_read_selection_reuses_growing_arithmetic_prefixes() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let raw = MachineTerm::MemoryLoad(
            intern_memory(Memory::new()),
            Box::new(Pointer::symbolic(Variable(994110))),
            LoadKind::Int32,
        );
        let leaf = KernelTermImport::default().machine(MachineIntegerType::Int32, &raw);
        let mut root = leaf.clone();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::arithmetic_binary(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                )
                .unwrap();
                let reads = crate::kernel::shared_machine_read_leaves(&root, || {
                    crate::instrumentation::record_deterministic_work(1);
                    true
                })
                .unwrap();
                assert_eq!(reads.len(), 1);
                assert_eq!(reads.get(&leaf.id()), Some(&leaf));
                let uses = crate::kernel::shared_machine_read_uses(&root, Some(4), || {
                    crate::instrumentation::record_deterministic_work(1);
                    true
                })
                .unwrap();
                assert_eq!(uses.len(), 1);
                assert_eq!(uses.get(&(leaf.id(), Some(4))), Some(&leaf));
            }
        });
        assert!(work <= 16 * size + 8, "size={size} work={work}");
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[test]
fn nested_read_address_import_is_linear_beside_unrelated_memory() {
    for unrelated in [0, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut memory = Memory::new();
        for index in 0..unrelated {
            memory = memory.store(
                Pointer::symbolic(Variable(997000 + index)),
                ProgramValue::Int32(MachineTerm::constant(index as u32)),
            );
        }
        let memory = intern_memory(memory);
        for depth in [16, 64, 256] {
            let mut raw = MachineTerm::constant(0);
            for _ in 0..depth {
                raw = MachineTerm::MemoryLoad(
                    memory.clone(),
                    Box::new(Pointer {
                        block: PointerBlock::Symbolic(Variable(996999)),
                        offset: PointerOffsetTerm::scaled_int32_node(raw, 4),
                    }),
                    LoadKind::Int32,
                );
            }
            let (term, work) = crate::instrumentation::measure_deterministic_work(|| {
                KernelTermImport::default().machine(MachineIntegerType::Int32, &raw)
            });
            assert!(matches!(term.node(), KernelTermNode::MemoryLoad { .. }));
            assert_eq!(KernelTermExport::machine(&term).unwrap(), raw);
            assert!(
                work <= 5 * depth + 5,
                "depth={depth}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn conditional_observation_retyping_matches_native_import_without_expanding_dags() {
    let _session = crate::kernel::VerificationSession::enter();
    let unsigned = MachineIntegerType::UInt32;
    let signed = MachineIntegerType::Int32;
    let a = MachineTerm::Variable(Variable(995910));
    let b = MachineTerm::Variable(Variable(995911));
    let guard = ConditionTerm::unsigned_less_equal(a.clone(), b.clone());
    let native = MachineTerm::If {
        condition: Box::new(guard.clone()),
        then_term: Box::new(a.clone()),
        else_term: Box::new(b),
    };
    let mut import = KernelTermImport::default();
    let original = import.machine_arithmetic(unsigned, &native).unwrap();
    let expected = import.machine_arithmetic(signed, &native).unwrap();
    assert_eq!(original.with_machine_observation_type(signed), expected);
    assert_eq!(expected.with_machine_observation_type(unsigned), original);
    let guard = import.condition(&guard);
    for size in [16, 64, 256] {
        let mut root = original.clone();
        for _ in 0..size {
            root = KernelTerm::machine_if_shared(unsigned, [guard.clone(), root.clone(), root]);
        }
        let exports = KernelTermExport::machine_export_count();
        let (signed_root, work) = crate::instrumentation::measure_deterministic_work(|| {
            root.with_machine_observation_type(signed)
        });
        assert!(work <= 3 * (size + 1), "size={size}, work={work}");
        let (_, repeated) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(root.with_machine_observation_type(signed), signed_root);
        });
        assert_eq!(repeated, 0);
        assert_eq!(signed_root.with_machine_observation_type(unsigned), root);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[test]
fn shared_read_descriptor_identity_does_not_expand_offset_dags() {
    use std::hash::{Hash, Hasher};
    let _session = crate::kernel::VerificationSession::enter();
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| {
                KernelTerm::variable(
                    KernelType::Program(ProgramType::Int32),
                    Variable(1017500 + i),
                )
            })
            .collect::<Vec<_>>();
        let memory = intern_memory(Memory::new());
        for size in [16, 64, 256] {
            let mut offset = KernelPointerOffset::Constant(0).into_shared().unwrap();
            for _ in 0..size {
                offset = KernelPointerOffset::Add([offset.clone(), offset])
                    .into_shared()
                    .unwrap();
            }
            let address = SharedPointerAddress::new(
                SharedPointerBlock::import(&PointerBlock::Symbolic(Variable(1017100))),
                offset,
            );
            let exports = KernelTermExport::machine_export_count();
            let ((first, second), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let first = KernelTerm::shared_scalar_read_descriptor(
                        MachineIntegerType::Int32,
                        &memory,
                        &address,
                        LoadKind::Int32,
                    );
                    let second = KernelTerm::shared_scalar_read_descriptor(
                        MachineIntegerType::Int32,
                        &memory,
                        &address,
                        LoadKind::Int32,
                    );
                    let mut hasher = std::collections::hash_map::DefaultHasher::new();
                    first.hash(&mut hasher);
                    second.hash(&mut hasher);
                    let _ = hasher.finish();
                    (first, second)
                });
            assert_eq!(first, second);
            assert!(first.0.machine_leaf.0.get().is_none());
            assert!(
                work <= 64,
                "size={size}, unrelated={unrelated}, work={work}"
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}

#[test]
fn repeated_scalar_read_imports_reuse_live_address_components() {
    let _session = crate::kernel::VerificationSession::enter();
    for size in [16, 64, 256] {
        let mut index =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1017900));
        for _ in 0..size {
            index = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [index.clone(), index],
            );
        }
        let pointer = Pointer {
            block: PointerBlock::Concrete("shared-read-hot".into()),
            offset: PointerOffsetTerm::Int32Scaled {
                value: SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, index)
                    .unwrap(),
                byte_width: 4,
            },
        };
        let memory = intern_memory(Memory::new());
        let retained = KernelTerm::scalar_read_descriptor(
            MachineIntegerType::Int32,
            &memory,
            &pointer,
            LoadKind::Int32,
        )
        .unwrap();
        for unrelated in [0, 128, 512] {
            let _unrelated = (0..unrelated)
                .map(|n| {
                    KernelPointerOffset::Variable(Variable(1017901 + n))
                        .into_shared()
                        .unwrap()
                })
                .collect::<Vec<_>>();
            let exports = KernelTermExport::machine_export_count();
            let (again, work) = crate::instrumentation::measure_deterministic_work(|| {
                KernelTerm::scalar_read_descriptor(
                    MachineIntegerType::Int32,
                    &memory,
                    &pointer,
                    LoadKind::Int32,
                )
                .unwrap()
            });
            assert_eq!(again, retained);
            assert!(work <= 24, "size={size} unrelated={unrelated} work={work}");
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(again.0.machine_leaf.0.get().is_none());
        }
    }
}

#[test]
fn pointer_read_roots_and_handoffs_do_not_expand_defining_address_dags() {
    let _session = crate::kernel::VerificationSession::enter();
    for unrelated in [0, 128, 512] {
        let mut memory = Memory::new();
        for n in 0..unrelated {
            memory = memory.with_block(format!("pointer-read-unrelated-{n}"), 8);
        }
        let memory = intern_memory(memory);
        let value = SharedPointerValue::import(&PointerValue::new(
            Pointer::symbolic(Variable(1018100)),
            ProgramType::Int32Pointer,
        ));
        for size in [16, 64, 256] {
            let mut offset = KernelPointerOffset::Constant(0).into_shared().unwrap();
            for _ in 0..size {
                offset = KernelPointerOffset::Add([offset.clone(), offset])
                    .into_shared()
                    .unwrap();
            }
            let address = SharedPointerAddress::new(
                SharedPointerBlock::import(&PointerBlock::Symbolic(Variable(1018101))),
                offset,
            );
            let exports = KernelTermExport::machine_export_count();
            let (root, work) = crate::instrumentation::measure_deterministic_work(|| {
                let root =
                    KernelTerm::shared_pointer_read(value.clone(), memory.clone(), address.clone());
                assert_eq!(
                    root,
                    KernelTerm::shared_pointer_read(value.clone(), memory.clone(), address.clone())
                );
                let mut carried = crate::kernel::ExecutionValue::from(root.clone());
                for _ in 0..32 {
                    carried = carried.clone();
                }
                assert_eq!(carried.shared(), Some(&root));
                root
            });
            assert!(root.0.argument_leaf.get().is_none());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(work <= 32, "size={size} unrelated={unrelated} work={work}");
        }
    }
}

#[test]
fn formed_pointer_roots_keep_prepared_displacement_dags() {
    let _session = crate::kernel::VerificationSession::enter();
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|n| {
                KernelTerm::shared_pointer_value(SharedPointerValue::import(&PointerValue::new(
                    Pointer::symbolic(Variable(1022100 + n)),
                    ProgramType::Int32Pointer,
                )))
            })
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut offset = KernelPointerOffset::Constant(0).into_shared().unwrap();
            for _ in 0..size {
                offset = KernelPointerOffset::Add([offset.clone(), offset])
                    .into_shared()
                    .unwrap();
            }
            let source = SharedPointerValue::import(&PointerValue::new(
                Pointer::symbolic(Variable(1022700)),
                ProgramType::Int32Pointer,
            ));
            let mut payload = source.node().clone();
            payload.address =
                SharedPointerAddress::new(payload.address.node().block.clone(), offset);
            payload.designation = payload.address.clone();
            let payload = SharedPointerValue::new(payload);
            let exports = KernelTermExport::machine_export_count();
            let (root, work) = crate::instrumentation::measure_deterministic_work(|| {
                let root = KernelTerm::shared_pointer_value(payload.clone());
                assert_eq!(root, KernelTerm::shared_pointer_value(payload.clone()));
                let mut value = crate::kernel::ExecutionValue::from(root.clone());
                for _ in 0..32 {
                    value = value.clone();
                }
                assert_eq!(value.shared(), Some(&root));
                root
            });
            assert!(root.0.argument_leaf.get().is_none());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(work <= 32, "size={size} unrelated={unrelated} work={work}");
        }
    }
}

#[test]
fn pointer_arithmetic_roots_retain_operand_and_result_dags() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = SharedPointerValue::import(&PointerValue::new(
        Pointer::symbolic(Variable(1023100)),
        ProgramType::Int32Pointer,
    ));
    let base_root = KernelTerm::shared_pointer_value(base.clone());
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|n| {
                KernelTerm::variable(
                    KernelType::Program(ProgramType::Int32),
                    Variable(1023101 + n),
                )
            })
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut index =
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1023700));
            for _ in 0..size {
                index = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [index.clone(), index],
                );
            }
            let mut payload = base.node().clone();
            payload.address = SharedPointerAddress::new(
                payload.address.node().block.clone(),
                KernelPointerOffset::Int32Scaled {
                    value: index.clone(),
                    byte_width: 4,
                }
                .into_shared()
                .unwrap(),
            );
            let payload = SharedPointerValue::new(payload);
            let exports = KernelTermExport::machine_export_count();
            let (root, work) = crate::instrumentation::measure_deterministic_work(|| {
                let operands = [base_root.clone(), index.clone()];
                let root = KernelTerm::shared_pointer_arithmetic(
                    MachineBinaryOp::Add,
                    4,
                    operands.clone(),
                    payload.clone(),
                );
                assert_eq!(
                    root,
                    KernelTerm::shared_pointer_arithmetic(
                        MachineBinaryOp::Add,
                        4,
                        operands,
                        payload.clone()
                    )
                );
                let mut value = crate::kernel::ExecutionValue::from(root.clone());
                for _ in 0..32 {
                    value = value.clone();
                }
                assert_eq!(value.shared(), Some(&root));
                root
            });
            let KernelTermNode::PointerArithmetic { operands, .. } = root.node() else {
                panic!("arithmetic");
            };
            assert_eq!(operands[1], index);
            assert!(root.0.argument_leaf.get().is_none());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(work <= 32, "size={size} unrelated={unrelated} work={work}");
        }
    }
}

#[test]
fn pointer_numeric_observations_retain_prepared_dags_without_export() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = SharedPointerValue::import(&PointerValue::new(
        Pointer::symbolic(Variable(1024200)),
        ProgramType::Int32Pointer,
    ));
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|n| {
                KernelTerm::variable(
                    KernelType::Program(ProgramType::Int32),
                    Variable(1024201 + n),
                )
            })
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut index =
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1024800));
            for _ in 0..size {
                index = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [index.clone(), index],
                );
            }
            let address = SharedPointerAddress::new(
                pointer.node().address.node().block.clone(),
                KernelPointerOffset::Int32Scaled {
                    value: index,
                    byte_width: 4,
                }
                .into_shared()
                .unwrap(),
            );
            let exports = KernelTermExport::machine_export_count();
            let (numeric, work) = crate::instrumentation::measure_deterministic_work(|| {
                KernelTerm::shared_pointer_address_observation(
                    MachineIntegerType::UInt64,
                    address.clone(),
                    AddressObjectClass::NONE,
                )
            });
            assert!(
                matches!(numeric.node(), KernelTermNode::PointerAddress { address: a, .. } if a == &address)
            );
            assert!(numeric.0.machine_leaf.0.get().is_none());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(work <= 48, "size={size} unrelated={unrelated} work={work}");
        }
    }
}

#[test]
fn pointer_call_handoffs_retain_prepared_argument_dags() {
    let _session = crate::kernel::VerificationSession::enter();
    let value = SharedPointerValue::import(&PointerValue::new(
        Pointer::symbolic(Variable(1025200)),
        ProgramType::Int32Pointer,
    ));
    let memory = intern_memory(Memory::new());
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|n| KernelTerm::variable(KernelType::Integer, Variable(1025201 + n)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut argument =
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1025800));
            for _ in 0..size {
                argument = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [argument.clone(), argument],
                );
            }
            let exports = KernelTermExport::machine_export_count();
            let (root, work) = crate::instrumentation::measure_deterministic_work(|| {
                let call = KernelTerm::checked_call(
                    KernelType::Program(ProgramType::Int32Pointer),
                    "pointer_select".into(),
                    vec![argument.clone()],
                );
                KernelTerm::shared_pointer_call(call, value.clone())
            });
            let KernelTermNode::PointerCall { call, .. } = root.node() else {
                panic!("pointer call")
            };
            let KernelTermNode::Call { arguments, .. } = call.node() else {
                panic!("call")
            };
            assert_eq!(arguments[0], argument);
            assert!(root.0.argument_leaf.get().is_none());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(work <= 48, "size={size} unrelated={unrelated} work={work}");
            let (reference, work) = crate::instrumentation::measure_deterministic_work(|| {
                KernelTerm::shared_array_reference(memory.clone(), root.clone(), ProgramType::Int32)
            });
            let KernelTermNode::ArrayReference { pointer, .. } = reference.node() else {
                panic!("array argument")
            };
            assert_eq!(pointer, &root);
            assert!(reference.0.argument_leaf.get().is_none());
            assert!(root.0.argument_leaf.get().is_none());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(
                work <= 16,
                "size={size} unrelated={unrelated} array work={work}"
            );
        }
    }
}

#[test]
fn boolean_guard_views_do_not_export_growing_prefixes() {
    for unrelated in [0, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Bool, Variable(965_000 + i)))
            .collect::<Vec<_>>();
        let yes = KernelTerm::intern(KernelType::Bool, KernelTermNode::BoolLiteral(true));
        let no = KernelTerm::intern(KernelType::Bool, KernelTermNode::BoolLiteral(false));
        for size in [16, 64, 256] {
            let mut guard = KernelTerm::variable(KernelType::Bool, Variable(966_000));
            for _ in 0..size {
                guard = KernelTerm::intern(
                    KernelType::Bool,
                    KernelTermNode::BoolIf {
                        arguments: [guard, yes.clone(), no.clone()],
                    },
                );
            }
            let arm = KernelTermImport::default()
                .machine(MachineIntegerType::Int32, &MachineTerm::constant(1));
            let root = KernelTerm::intern(
                KernelType::Program(ProgramType::Int32),
                KernelTermNode::MachineIf {
                    arguments: [guard.clone(), arm.clone(), arm.clone()],
                },
            );
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    let (view, arms) = MachineOperandView::Shared(&root)
                        .conditional_view()
                        .unwrap();
                    assert!(matches!(view, BooleanOperandView::Shared(value) if value == &guard));
                    let [_, yes, no] = view.conditional().unwrap();
                    assert_eq!(yes.constant(), Some(true));
                    assert_eq!(no.constant(), Some(false));
                    assert!(matches!(arms[0], MachineOperandView::Shared(value) if value == &arm));
                }
            });
            assert_eq!(
                work, 0,
                "borrowed inspection: size={size}, unrelated={unrelated}"
            );
        }
    }
}

#[test]
fn boolean_dependency_walk_visits_shared_connectives_once() {
    for size in [16, 64, 256] {
        let atom = KernelTerm::variable(KernelType::Bool, Variable(967_000));
        let mut root = atom.clone();
        for _ in 0..size {
            root = KernelTerm::intern(
                KernelType::Bool,
                KernelTermNode::BoolEqual {
                    arguments: [root.clone(), root],
                },
            );
        }
        let (count, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut count = 0;
            BooleanOperandView::Shared(&root).for_each_dependency_leaf(|leaf| {
                assert!(matches!(leaf, BooleanOperandView::Shared(value) if value == &atom));
                count += 1;
            });
            count
        });
        assert_eq!(count, 1);
        assert_eq!(work, size + 1);
    }
}

#[test]
fn growing_common_boolean_comparisons_keep_operands_shared() {
    use crate::kernel::assumptions::boolean_operands_equal_with_load_atoms;
    use crate::kernel::{BooleanOperandView as B, KernelTermNode};
    let mut samples = Vec::new();
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let read = |block: &str| {
            let memory =
                crate::kernel::intern_memory(crate::kernel::Memory::new().with_block(block, 16));
            let pointer = crate::kernel::Pointer {
                block: block.into(),
                offset: crate::kernel::PointerOffsetTerm::Constant(0),
            };
            KernelTermImport::default().machine(
                format,
                &MachineTerm::MemoryLoad(memory, Box::new(pointer), crate::kernel::LoadKind::Int32),
            )
        };
        let mut left = read("bool-left");
        let mut right = read("bool-right");
        let zero =
            crate::kernel::KernelTermImport::default().machine(format, &MachineTerm::constant(0));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                for root in [&mut left, &mut right] {
                    *root = KernelTerm::machine_binary_shared(
                        format,
                        MachineBinaryOp::Add,
                        [root.clone(), root.clone()],
                    );
                }
                let comparison = |root: KernelTerm| {
                    KernelTerm::intern(
                        KernelType::Bool,
                        KernelTermNode::BoolCompare {
                            format,
                            relation: CompareRelation::LessThan,
                            arguments: [root, zero.clone()],
                        },
                    )
                };
                let l = comparison(left.clone());
                let r = comparison(right.clone());
                assert!(boolean_operands_equal_with_load_atoms(
                    B::Shared(&l),
                    B::Shared(&r),
                    &|_, _| true
                ));
                assert!(!boolean_operands_equal_with_load_atoms(
                    B::Shared(&l),
                    B::Shared(&r),
                    &|_, _| false
                ));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|p| p[1] <= p[0] * 5 + 100),
        "{samples:?}"
    );
}

#[test]
fn common_boolean_identity_visits_shared_connectives_once() {
    use crate::kernel::BooleanOperandView as B;
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let atom = |format| {
            KernelTermImport::default().condition(&ConditionTerm::Compare {
                format,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(Variable(964_099))),
                right: Box::new(MachineTerm::constant(1)),
            })
        };
        let mut left = atom(MachineIntegerType::Int32);
        let mut right = atom(MachineIntegerType::UInt32);
        for _ in 0..size {
            left = KernelTerm::intern(
                KernelType::Bool,
                KernelTermNode::BoolEqual {
                    arguments: [left.clone(), left],
                },
            );
            right = KernelTerm::intern(
                KernelType::Bool,
                KernelTermNode::BoolEqual {
                    arguments: [right.clone(), right],
                },
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(B::Shared(&left).syntax_equal(B::Shared(&right)));
        });
        assert!(work <= size * 3 + 20, "{size}: {work}");
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[test]
fn boolean_substitution_retains_shared_connective_prefixes() {
    for size in [16, 64, 256] {
        let variable = Variable(968_000);
        let mut root = KernelTerm::variable(KernelType::Bool, variable);
        for _ in 0..size {
            root = KernelTerm::intern(
                KernelType::Bool,
                KernelTermNode::BoolEqual {
                    arguments: [root.clone(), root],
                },
            );
        }
        let (mut rewritten, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::reasoning::substitute_bitvector_variable_in_common_condition(
                &root,
                variable,
                &MachineTerm::constant(1),
            )
            .unwrap()
        });
        assert!(work <= 12 * (size + 1), "size={size}, work={work}");
        for _ in 0..size {
            let KernelTermNode::BoolEqual { arguments } = rewritten.node() else {
                panic!("unfolded equality")
            };
            assert_eq!(arguments[0], arguments[1]);
            rewritten = arguments[0].clone();
        }
        // An Int32 word is not a typed Bool literal. Preserve the native
        // truth conversion, including its explicit UInt8 comparison.
        let expected = KernelTermImport::default().condition(&ConditionTerm::truth_of_bool_word(
            &MachineTerm::constant(1),
        ));
        assert_eq!(rewritten, expected);
    }
}

#[test]
fn boolean_substitution_reuses_overlapping_arithmetic_operands() {
    let mut samples = Vec::new();
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let source = Variable(971_150);
        let mut word = KernelTerm::variable(KernelType::Program(format.program_type()), source);
        let factor = KernelTerm::variable(
            KernelType::Program(format.program_type()),
            Variable(971_151),
        );
        let zero = KernelTermImport::default().machine(format, &MachineTerm::constant(0));
        let mut condition = KernelTermImport::default().condition(&ConditionTerm::Constant(true));
        for _ in 0..size {
            word = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Multiply,
                [word, factor.clone()],
            );
            let atom = KernelTerm::boolean_comparison_raw(
                format,
                CompareRelation::LessThan,
                [word.clone(), zero.clone()],
            );
            condition = KernelTerm::boolean_equal_raw([condition, atom]);
        }
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let result =
                crate::kernel::reasoning::substitute_bitvector_variable_in_common_condition(
                    &condition,
                    source,
                    &MachineTerm::Variable(Variable(971_152)),
                )
                .unwrap();
            assert_ne!(result, condition);
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|p| p[1] <= 5 * p[0] + 100),
        "{samples:?}"
    );
}

#[test]
fn refused_boolean_transport_does_not_export_shared_guard_prefixes() {
    for size in [16, 64, 256] {
        let mut root = KernelTerm::variable(KernelType::Bool, Variable(969_000));
        for _ in 0..size {
            root = KernelTerm::intern(
                KernelType::Bool,
                KernelTermNode::BoolEqual {
                    arguments: [root.clone(), root],
                },
            );
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                assert!(
                    crate::kernel::memory_provenance::transport_framed_common_condition(
                        &root,
                        &Memory::new(),
                        None
                    )
                    .is_none()
                );
            }
        });
        assert!(work <= size, "size={size}, work={work}");
    }
}

#[test]
fn boolean_transport_keeps_shared_arithmetic_operands() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut operand = KernelTerm::variable(
            KernelType::Program(format.program_type()),
            Variable(972_010),
        );
        for _ in 0..size {
            operand = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [operand.clone(), operand],
            );
        }
        let zero = KernelTermImport::default().machine(format, &MachineTerm::constant(0));
        let guard =
            KernelTerm::boolean_comparison_raw(format, CompareRelation::LessThan, [operand, zero]);
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let actual = crate::kernel::memory_provenance::transport_framed_common_condition(
                &guard,
                &Memory::new(),
                None,
            )
            .unwrap();
            assert_eq!(actual, guard);
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|p| p[1] <= p[0] * 5 + 100),
        "{samples:?}"
    );
}
