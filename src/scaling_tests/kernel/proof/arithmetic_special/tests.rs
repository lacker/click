// Scaling tests of `src/kernel/proof/arithmetic_special.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::CompareRelation;
use crate::kernel::MachineBinaryOp;
use crate::kernel::MachineIntegerType;
use crate::kernel::binary_node;
use crate::kernel::{MachineCastSpelling, MachineTerm};

#[test]
fn cast_identity_reads_interned_integer_operands_without_walking_their_dags() {
    use crate::kernel::{IntegerTerm, MachineIntegerType, Variable};
    let mut samples = Vec::new();
    for size in [8, 32, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut value = IntegerTerm::Variable(Variable(892_000));
        for index in 0..size {
            value = IntegerTerm::add(value, IntegerTerm::Variable(Variable(893_000 + index)));
        }
        let cast = MachineTerm::IntegerToMachine {
            value: value.into(),
            destination: MachineIntegerType::Int64,
        };
        let duplicate = cast.clone();
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            bitvector_equal(&cast, &duplicate)
        });
        assert!(equal);
        assert!(work <= 16, "{size}: {work}");
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
}

#[test]
fn computed_index_translation_checks_bounds_and_scales_with_payload() {
    let mut previous = None;
    for size in [2usize, 8, 32, 96] {
        let p = PointerOffsetTerm::Variable(crate::kernel::Variable(100));
        let arr = PointerOffsetTerm::Variable(crate::kernel::Variable(101));
        let mut index = MachineTerm::legacy_cast(
            MachineCastSpelling::UInt32From64,
            Box::new(MachineTerm::Variable(crate::kernel::Variable(1))),
        );
        for _ in 0..size {
            index = binary_node!(
                Int32,
                Subtract,
                Box::new(index),
                Box::new(MachineTerm::constant(0))
            );
        }
        let relation = pointer_eq(p.clone(), add(arr.clone(), scaled(index.clone())));
        let bound = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(index.clone()),
                right: Box::new(MachineTerm::constant(i32::MAX as u32)),
            },
            true,
        );
        let goal = pointer_eq(
            add(p, PointerOffsetTerm::Constant(4)),
            add(
                arr,
                scaled(binary_node!(
                    Int32,
                    Add,
                    Box::new(index),
                    Box::new(MachineTerm::constant(1)),
                )),
            ),
        );
        let certificate = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerTranslation {
                relation: 0,
                bounds: vec![1],
                result: goal.clone(),
            }],
            conclusion: 0,
        };
        let (valid, work) = crate::instrumentation::measure_deterministic_work(|| {
            certificate.check(&goal, &[relation.clone(), bound]).is_ok()
        });
        assert!(valid, "computed index of size {size}");
        if let Some((previous_size, previous_work)) = previous {
            assert!(
                work <= previous_work * (size / previous_size) + 40,
                "{size}: {work} after {previous_work}"
            );
        }
        previous = Some((size, work));
        let no_bound = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerTranslation {
                relation: 0,
                bounds: vec![],
                result: goal.clone(),
            }],
            conclusion: 0,
        };
        assert!(no_bound.check(&goal, &[relation]).is_err());
    }
}

// Tag projection needs exactly the selected base alignment, preserves all
// selected bits, and pays for the written word rather than a search context.
#[test]
fn pointer_tag_reads_require_alignment_and_scale_with_word_syntax() {
    let base = pointer(PointerOffsetTerm::Constant(0));
    let alignment = Proposition::ConditionIs(ConditionTerm::pointer_aligned(base.clone(), 8), true);
    let address = MachineTerm::PointerAddress(
        Box::new(base.clone()),
        crate::kernel::AddressObjectClass::NONE,
    );
    let value = MachineTerm::Variable(crate::kernel::Variable(71_001));
    let mask =
        |term, bits| MachineTerm::uint64_bitwise_and(term, MachineTerm::uint64_constant(bits));
    let equality =
        |left, right| Proposition::ConditionIs(ConditionTerm::uint64_equal(left, right), true);
    let check = |goal: &Proposition, premises: &[Proposition]| {
        SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerWordFromAlignment {
                alignments: (0..premises.len()).collect(),
                result: goal.clone(),
            }],
            conclusion: 0,
        }
        .check(goal, premises)
    };
    let tagged = MachineTerm::uint64_bitwise_or(mask(value.clone(), 7), address.clone());
    let goal = equality(mask(tagged.clone(), 3), mask(value.clone(), 3));
    assert!(check(&goal, std::slice::from_ref(&alignment)).is_ok());
    assert!(check(&goal, &[]).is_err());
    let insufficient =
        Proposition::ConditionIs(ConditionTerm::pointer_aligned(base.clone(), 2), true);
    assert!(check(&goal, &[insufficient]).is_err());
    let other = pointer(PointerOffsetTerm::Constant(1));
    let foreign = Proposition::ConditionIs(ConditionTerm::pointer_aligned(other, 8), true);
    assert!(check(&goal, &[foreign]).is_err());
    let changed_tag = equality(mask(tagged.clone(), 3), mask(value.clone(), 1));
    assert!(check(&changed_tag, std::slice::from_ref(&alignment)).is_err());
    let changed_mask = equality(mask(tagged, 7), mask(value.clone(), 3));
    assert!(check(&changed_mask, std::slice::from_ref(&alignment)).is_err());

    let word = MachineTerm::Variable(crate::kernel::Variable(71_002));
    let relation = equality(
        word.clone(),
        MachineTerm::uint64_add(address.clone(), mask(value.clone(), 1)),
    );
    let read = equality(mask(word, 1), mask(value, 1));
    SpecialArithmeticCertificate {
        nodes: vec![SpecialArithmeticNode::PointerWordEquality {
            relation: 0,
            alignments: vec![1],
            result: read.clone(),
        }],
        conclusion: 0,
    }
    .check(&read, &[relation, alignment.clone()])
    .unwrap();

    let mut previous = 0;
    for size in [8, 16, 32, 64] {
        let mut word = address.clone();
        for _ in 0..size {
            word = MachineTerm::uint64_add(word, MachineTerm::uint64_constant(2));
        }
        let goal = equality(mask(word, 1), MachineTerm::uint64_constant(0));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            check(&goal, std::slice::from_ref(&alignment))
        });
        assert!(result.is_ok(), "size {size}, goal {goal:?}");
        assert!(work > 0);
        if previous > 0 {
            assert!(work <= previous * 3, "{size}: {work} after {previous}");
        }
        previous = work;
    }
}

#[test]
fn tagged_word_alignment_index_scales_with_alignment_count() {
    let base_pointer = pointer(PointerOffsetTerm::Constant(0));
    let address = MachineTerm::PointerAddress(
        Box::new(base_pointer.clone()),
        crate::kernel::AddressObjectClass::NONE,
    );
    let word = MachineTerm::Variable(crate::kernel::Variable(12));
    let relation = Proposition::ConditionIs(
        ConditionTerm::uint64_equal(
            word.clone(),
            MachineTerm::uint64_add(address.clone(), MachineTerm::uint64_constant(1)),
        ),
        true,
    );
    let mut deep_word = word.clone();
    for _ in 0..64 {
        deep_word = MachineTerm::uint64_add(deep_word, MachineTerm::uint64_constant(0));
    }
    let goal = Proposition::ConditionIs(
        ConditionTerm::uint64_equal(
            MachineTerm::uint64_bitwise_or(deep_word, MachineTerm::uint64_constant(2)),
            MachineTerm::uint64_add(address, MachineTerm::uint64_constant(3)),
        ),
        true,
    );
    let low_alignment = Proposition::ConditionIs(
        ConditionTerm::pointer_aligned(base_pointer.clone(), 2),
        true,
    );
    let alignment = Proposition::ConditionIs(ConditionTerm::pointer_aligned(base_pointer, 8), true);
    let mut previous = None;
    for size in [1, 4, 16, 64, 256, 1024] {
        let mut premises = vec![relation.clone()];
        premises.extend((1..size).map(|_| low_alignment.clone()));
        premises.push(alignment.clone());
        let certificate = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                relation: 0,
                alignments: (1..=size).collect(),
                result: goal.clone(),
            }],
            conclusion: 0,
        };
        let (valid, work) = crate::instrumentation::measure_deterministic_work(|| {
            certificate.check(&goal, &premises).is_ok()
        });
        assert!(valid);
        if let Some(previous) = previous {
            assert!(work <= previous * 4);
        }
        previous = Some(work);
    }
}

#[test]
fn direct_tagged_word_checker_does_not_scan_unrelated_alignments() {
    let base_pointer = pointer(PointerOffsetTerm::Constant(0));
    let address = MachineTerm::PointerAddress(
        Box::new(base_pointer.clone()),
        crate::kernel::AddressObjectClass::NONE,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::uint64_equal(
            MachineTerm::uint64_bitwise_or(
                MachineTerm::uint64_add(address.clone(), MachineTerm::uint64_constant(1)),
                MachineTerm::uint64_constant(2),
            ),
            MachineTerm::uint64_add(address, MachineTerm::uint64_constant(3)),
        ),
        true,
    );
    let alignment = Proposition::ConditionIs(ConditionTerm::pointer_aligned(base_pointer, 8), true);
    let mut previous = None;
    for size in [1, 8, 32, 128, 256] {
        let mut premises = vec![alignment.clone()];
        premises.extend((0..size).map(|index| {
            Proposition::ConditionIs(
                ConditionTerm::pointer_aligned(
                    pointer(PointerOffsetTerm::Variable(crate::kernel::Variable(
                        1000 + index,
                    ))),
                    8,
                ),
                true,
            )
        }));
        let certificate = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerWordFromAlignment {
                alignments: vec![0],
                result: goal.clone(),
            }],
            conclusion: 0,
        };
        let (valid, work) = crate::instrumentation::measure_deterministic_work(|| {
            certificate.check(&goal, &premises).is_ok()
        });
        assert!(valid);
        if let Some(previous) = previous {
            assert!(
                work <= previous * 2,
                "unrelated alignment work: {work} vs {previous}"
            );
        }
        previous = Some(work);
    }
}

#[test]
fn translation_work_scales_with_explicit_payload() {
    let mut previous = None;
    for size in [4, 8, 16, 32, 64] {
        let p = PointerOffsetTerm::Variable(crate::kernel::Variable(100));
        let arr = PointerOffsetTerm::Variable(crate::kernel::Variable(101));
        let i = MachineTerm::Variable(crate::kernel::Variable(1));
        let n = MachineTerm::Variable(crate::kernel::Variable(2));
        let mut left = p.clone();
        let mut right = add(arr.clone(), scaled(i.clone()));
        let mut premises = vec![Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(i.clone()),
                right: Box::new(n.clone()),
            },
            true,
        )];
        for index in 0..size {
            let delta = PointerOffsetTerm::Variable(crate::kernel::Variable(1000 + index));
            left = add(left, delta.clone());
            right = add(right, delta);
            premises.push(Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(MachineTerm::Variable(crate::kernel::Variable(2000 + index))),
                    right: Box::new(MachineTerm::constant(100)),
                },
                true,
            ));
        }
        let relation = pointer_eq(p, add(arr, scaled(i)));
        let goal = pointer_eq(left, right);
        premises.insert(0, relation);
        let certificate = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerTranslation {
                relation: 0,
                bounds: (1..premises.len()).collect(),
                result: goal.clone(),
            }],
            conclusion: 0,
        };
        let (valid, work) = crate::instrumentation::measure_deterministic_work(|| {
            certificate.check(&goal, &premises).is_ok()
        });
        assert!(valid);
        if let Some(previous) = previous {
            assert!(work <= previous * 4);
        }
        previous = Some(work);
    }
}

#[test]
fn tagged_word_traversal_scales_with_tagged_depth() {
    let mut previous = None;
    for depth in [4, 8, 16, 32, 64] {
        let address = MachineTerm::PointerAddress(
            Box::new(pointer(PointerOffsetTerm::Constant(0))),
            crate::kernel::AddressObjectClass::NONE,
        );
        let variable = MachineTerm::Variable(crate::kernel::Variable(94));
        let mut tagged = address;
        for _ in 0..depth {
            tagged = MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Add,
                left: Box::new(tagged),
                right: Box::new(MachineTerm::uint64_constant(1)),
            };
        }
        let relation = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(variable.clone()),
                right: Box::new(tagged),
            },
            true,
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(variable.clone()),
                right: Box::new(variable),
            },
            true,
        );
        let certificate = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                relation: 0,
                alignments: vec![],
                result: goal.clone(),
            }],
            conclusion: 0,
        };
        let (valid, work) = crate::instrumentation::measure_deterministic_work(|| {
            certificate
                .check(&goal, std::slice::from_ref(&relation))
                .is_ok()
        });
        assert!(valid);
        if let Some(previous) = previous {
            assert!(work <= previous * 4);
        }
        previous = Some(work);
    }
}

#[test]
fn tagged_word_symbolic_tag_chains_scale_without_rewalking_tags() {
    let mut previous = None;
    for depth in [4, 8, 16, 32, 64] {
        let address = MachineTerm::PointerAddress(
            Box::new(pointer(PointerOffsetTerm::Constant(0))),
            crate::kernel::AddressObjectClass::NONE,
        );
        let variable = MachineTerm::Variable(crate::kernel::Variable(194));
        let mut tagged = address;
        for index in 0..depth {
            tagged = MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Add,
                left: Box::new(tagged),
                right: Box::new(MachineTerm::Variable(crate::kernel::Variable(200 + index))),
            };
        }
        let relation = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(variable.clone()),
                right: Box::new(tagged),
            },
            true,
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(variable.clone()),
                right: Box::new(variable),
            },
            true,
        );
        let certificate = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                relation: 0,
                alignments: vec![],
                result: goal.clone(),
            }],
            conclusion: 0,
        };
        let (valid, work) = crate::instrumentation::measure_deterministic_work(|| {
            certificate
                .check(&goal, std::slice::from_ref(&relation))
                .is_ok()
        });
        assert!(valid);
        if let Some(previous) = previous {
            assert!(work <= previous * 4);
        }
        previous = Some(work);
    }
}

#[test]
fn checker_validates_unselected_nodes_and_scales_without_cloning_results() {
    let value = MachineTerm::Variable(crate::kernel::Variable(91));
    let finite = Proposition::ConditionIs(
        ConditionTerm::float32_classification(value.clone(), FloatClassification::Finite),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::float32_compare(value.clone(), value, ComparisonOperator::Equal),
        true,
    );
    let mut nodes = vec![SpecialArithmeticNode::FloatReflexive {
        finite: 0,
        result: goal.clone(),
    }];
    nodes.extend((0..1024).map(|_| SpecialArithmeticNode::FloatReflexive {
        finite: usize::MAX,
        result: Proposition::ConditionIs(ConditionTerm::Constant(false), true),
    }));
    let invalid = SpecialArithmeticCertificate {
        nodes,
        conclusion: 0,
    };
    assert!(matches!(
        invalid.check(&goal, std::slice::from_ref(&finite)),
        Err(SpecialArithmeticCheckError::InvalidPremise(usize::MAX))
    ));

    let mut previous = None;
    for size in [1, 4, 16, 64, 256, 1024] {
        let nodes = (0..size)
            .map(|_| SpecialArithmeticNode::FloatReflexive {
                finite: 0,
                result: goal.clone(),
            })
            .collect();
        let certificate = SpecialArithmeticCertificate {
            nodes,
            conclusion: 0,
        };
        let (valid, work) = crate::instrumentation::measure_deterministic_work(|| {
            certificate
                .check(&goal, std::slice::from_ref(&finite))
                .is_ok()
        });
        assert!(valid);
        if let Some(previous) = previous {
            assert!(work <= previous * 4);
        }
        previous = Some(work);
    }
}

#[test]
fn unsigned_widening_identity_work_scales_with_operand_payload() {
    let mut samples = Vec::new();
    for size in [4, 16, 64, 96] {
        let mut value = MachineTerm::Variable(crate::kernel::Variable(994_111));
        for _ in 0..size {
            value = binary_node!(
                Int32,
                Add,
                Box::new(value),
                Box::new(MachineTerm::constant(0))
            );
        }
        let widened = MachineTerm::legacy_cast(MachineCastSpelling::UInt64From32, Box::new(value));
        let (same, work) = crate::instrumentation::measure_deterministic_work(|| {
            bitvector_equal(&widened, &widened)
        });
        assert!(same);
        assert!(work <= size * 8 + 8, "{size}: {work}");
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * pair[1].0.div_ceil(pair[0].0),
            "{samples:?}"
        );
    }
}

#[test]
fn signed_defined_certificates_keep_shared_operands_and_source_bounds() {
    use crate::kernel::{IntegerTerm, KernelTerm, KernelType, SharedMachineIntegerTerm, Variable};
    for (format, width) in [
        (MachineIntegerType::Int32, SignedDefinedWidth::Int32),
        (MachineIntegerType::Int64, SignedDefinedWidth::Int64),
    ] {
        let mut samples = Vec::new();
        for size in [8, 32, 96] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut term =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(982600));
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    term = KernelTerm::machine_binary_shared(
                        format,
                        MachineBinaryOp::Add,
                        [term.clone(), term.clone()],
                    );
                    let observation =
                        SharedMachineIntegerTerm::from_shared(format, term.clone()).unwrap();
                    let observed = IntegerTerm::Machine(observation.clone());
                    let premises = [
                        Proposition::ConditionIs(
                            ConditionTerm::integer_less_equal(
                                observed.clone(),
                                IntegerTerm::constant(100.into()),
                            ),
                            true,
                        ),
                        Proposition::ConditionIs(
                            ConditionTerm::integer_greater_equal(
                                observed.clone(),
                                IntegerTerm::constant((-100).into()),
                            ),
                            true,
                        ),
                    ];
                    let exact = crate::kernel::machine_integer::Operation::Add
                        .exact(observed, IntegerTerm::constant(1.into()));
                    let (minimum, maximum) = width.range();
                    let goal = Proposition::And(
                        Box::new(Proposition::ConditionIs(
                            ConditionTerm::integer_less_equal(
                                exact.clone(),
                                IntegerTerm::constant(maximum.into()),
                            ),
                            true,
                        )),
                        Box::new(Proposition::ConditionIs(
                            ConditionTerm::integer_greater_equal(
                                exact,
                                IntegerTerm::constant(minimum.into()),
                            ),
                            true,
                        )),
                    );
                    let certificate = SpecialArithmeticCertificate {
                        nodes: vec![SpecialArithmeticNode::SignedDefined {
                            width,
                            bounds: vec![0, 1],
                            result: goal.clone(),
                        }],
                        conclusion: 0,
                    };
                    assert_eq!(certificate.check(&goal, &premises), Ok(()));
                    let bad = [Proposition::ConditionIs(
                        ConditionTerm::Constant(true),
                        true,
                    )];
                    assert!(signed_defined(0, width, &[(0, &bad[0])], &goal).is_err());
                    assert!(!observation.has_boxed_operand());
                }
            });
            samples.push((size, work));
        }
        for pair in samples.windows(2) {
            let [(small, sw), (large, lw)] = pair else {
                unreachable!()
            };
            assert!(lw * small * 4 <= sw * large * 5, "{format:?}: {samples:?}");
        }
    }
}

#[test]
fn arithmetic_read_atoms_keep_state_identity_without_scanning_storage() {
    use crate::kernel::{LoadKind, Memory, ProgramValue, Variable, intern_memory};
    let mut samples = Vec::new();
    for size in [8, 64, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Pointer::symbolic(Variable(894_000));
        let mut memory = Memory::new();
        for index in 0..size {
            memory = memory.store(
                Pointer::symbolic(Variable(895_000 + index)),
                ProgramValue::Int32(MachineTerm::constant(7)),
            );
        }
        let memory = intern_memory(memory);
        let read =
            MachineTerm::MemoryLoad(memory.clone(), Box::new(address.clone()), LoadKind::Bits64);
        let duplicate = read.clone();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(charge_bitvector(&read));
            assert!(bitvector_equal(&read, &duplicate));
            assert_eq!(bounded_term_hash(&read), bounded_term_hash(&duplicate));
            assert!(bounded_term_hash(&read).is_some());
        });
        let changed = intern_memory(memory.memory().clone().store(
            address.clone(),
            ProgramValue::UInt64(MachineTerm::uint64_constant(9)),
        ));
        let different =
            MachineTerm::MemoryLoad(changed, Box::new(address.clone()), LoadKind::Bits64);
        assert!(!bitvector_equal(&read, &different));
        assert!(!bitvector_equal(
            &read,
            &MachineTerm::MemoryLoad(memory, Box::new(address), LoadKind::Int32)
        ));
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
}

#[test]
fn shared_tagged_word_certificates_preserve_bounds_without_exports() {
    use crate::kernel::{KernelTerm, KernelTermExport, MachineOperandView as View};
    let mut previous = None;
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let address = MachineTerm::PointerAddress(
            Box::new(pointer(PointerOffsetTerm::Constant(0))),
            crate::kernel::AddressObjectClass::NONE,
        );
        let mut root = KernelTerm::retained_machine_operand(format, View::Legacy(&address));
        let one = KernelTerm::retained_machine_operand(
            format,
            View::Legacy(&MachineTerm::uint64_constant(1)),
        );
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [root, one.clone()],
            );
        }
        let condition = crate::kernel::machine_integer::comparison::condition_for_operand_views(
            format,
            CompareRelation::Equal,
            [View::Shared(&root), View::Shared(&root)],
        );
        let goal = Proposition::ConditionIs(condition.clone(), true);
        let exports = KernelTermExport::machine_export_count();
        let (valid, work) = crate::instrumentation::measure_deterministic_work(|| {
            pointer_word_from_alignment(&[], &goal)
        });
        assert!(valid, "size={size}");
        assert!(!pointer_word_from_alignment(
            &[],
            &Proposition::ConditionIs(condition, false)
        ));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        if let Some(previous) = previous {
            assert!(
                work <= previous * 5,
                "size={size}, work={work}, previous={previous}"
            );
        }
        previous = Some(work);
    }
}
