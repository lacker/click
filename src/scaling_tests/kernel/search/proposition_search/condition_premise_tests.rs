// Scaling tests of `src/kernel/search/proposition_search.rs` (module `condition_premise_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::binary_node;
use crate::kernel::{CompareRelation, MachineIntegerType};

#[test]
fn refused_integer_equality_does_not_rebuild_connected_order_facts() {
    let left = IntegerTerm::var(Variable(791_001));
    let right = IntegerTerm::var(Variable(791_002));
    let goal = Proposition::ConditionIs(
        ConditionTerm::IntegerEqual(left.clone().into(), right.into()),
        true,
    );
    for size in [4u64, 16, 64, 256] {
        let mut context = PureFactContext::new();
        for index in 0..size {
            let sum = IntegerTerm::add(left.clone(), IntegerTerm::var(Variable(792_000 + index)));
            context = context.assume_condition(
                ConditionTerm::integer_less_equal(IntegerTerm::constant_i64(0), sum),
                true,
            );
        }
        // `solve` is slow part, and its condition match reads each fact a
        // bounded number of times; rebuilding the connected order facts per
        // fact would be quadratic.
        let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::search::ProofSearch::derive_solve_proposition(&(context), &goal)
        });
        assert!(derivation.is_none());
        let bound = 512 + 4 * size as usize;
        assert!(work <= bound, "{size} connected order facts: {work} work");
    }
}

#[test]
fn wide_condition_index_construction_charges_its_variable_entries() {
    let mut samples = Vec::new();
    for size in [4, 8, 16, 32] {
        let mut terms = (0..size)
            .map(|index| term(40_000 + (size * 100 + index) as u64))
            .collect::<Vec<_>>();
        while terms.len() > 1 {
            terms = terms
                .chunks(2)
                .map(|pair| {
                    if pair.len() == 1 {
                        pair[0].clone()
                    } else {
                        binary_node!(
                            Int32,
                            Add,
                            Box::new(pair[0].clone()),
                            Box::new(pair[1].clone())
                        )
                    }
                })
                .collect();
        }
        let condition = ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(terms.pop().unwrap()),
            right: Box::new(MachineTerm::constant(0)),
        };
        let ((context, work), events) = crate::instrumentation::collect(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                PureFactContext::new().assume_condition(condition, true)
            })
        });
        assert_eq!(
            context
                .condition_fact_pairs(crate::kernel::search::SearchPermission::new())
                .count(),
            1
        );
        let index_work = events
            .into_iter()
            .filter_map(|event| {
                if let crate::instrumentation::VerificationEvent::OperationFinished {
                    name,
                    work,
                    ..
                } = event
                {
                    (name == "condition variable indexing").then_some(work)
                } else {
                    None
                }
            })
            .sum::<usize>();
        // The existing context-entry charge covers the first variable.
        assert_eq!(index_work, size - 1);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] * 3),
        "{samples:?}"
    );
}

#[test]
fn state_condition_index_builds_once_and_survives_scalar_updates() {
    let mut cold_samples = Vec::new();
    let mut warm_samples = Vec::new();
    for size in [8, 16, 32, 64] {
        let (mut context, goal) = chain(8, 0);
        let memory = intern_memory(Memory::new().with_block("other", size as u32 * 4));
        for index in 0..size {
            let condition = ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(term(20_000 + index as u64)),
                right: Box::new(MachineTerm::MemoryLoad(
                    memory.clone(),
                    Box::new(Pointer {
                        block: "other".into(),
                        offset: PointerOffsetTerm::Constant(index as i64 * 4),
                    }),
                    crate::kernel::LoadKind::Int32,
                )),
            };
            context = context.assume_condition(condition, true);
        }
        let (selected, cold) = crate::instrumentation::measure_deterministic_work(|| {
            connected_condition_premises(&context, &goal, false).unwrap()
        });
        assert_eq!(selected.len(), 8);
        let (_, warm) = crate::instrumentation::measure_deterministic_work(|| {
            connected_condition_premises(&context, &goal, false).unwrap()
        });
        assert!(
            cold >= warm + size,
            "state construction must be charged: {cold}, {warm}"
        );
        cold_samples.push(cold);
        warm_samples.push(warm);
        let scalar_branch = context
            .clone()
            .assume_condition(order(30_000, 30_001), true);
        let (_, branch_work) = crate::instrumentation::measure_deterministic_work(|| {
            connected_condition_premises(&scalar_branch, &goal, false).unwrap()
        });
        assert_eq!(
            branch_work, warm,
            "scalar insertion must share the completed state index"
        );
        let extra = ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(term(90_000)),
            right: Box::new(MachineTerm::MemoryLoad(
                memory.clone(),
                Box::new(Pointer {
                    block: "other".into(),
                    offset: PointerOffsetTerm::Constant(0),
                }),
                crate::kernel::LoadKind::Int32,
            )),
        };
        let extended = scalar_branch.assume_condition(extra, true);
        let (selected, extended_work) = crate::instrumentation::measure_deterministic_work(|| {
            connected_condition_premises(&extended, &goal, false).unwrap()
        });
        assert_eq!(selected.len(), 8);
        assert!(
            extended_work > warm && extended_work <= warm + 8,
            "state insertion must apply only its delta: {extended_work}, {warm}"
        );
        eprintln!("state bucket {size}: cold {cold}, warm {warm}");
    }
    assert!(
        warm_samples.iter().all(|work| *work == warm_samples[0]),
        "{warm_samples:?}"
    );
    assert!(
        cold_samples.windows(2).all(|pair| pair[1] <= pair[0] * 3),
        "{cold_samples:?}"
    );
}

#[test]
#[ignore = "nightly: 4.8s in the parallel gate"]
fn connected_condition_selection_scales_linearly_in_chain_and_context() {
    for grow_chain in [false, true] {
        let mut samples = Vec::new();
        let mut complete = Vec::new();
        for size in [8, 16, 32, 64] {
            // Kernel interning is thread-local. Give every sample the same
            // cold tables instead of comparing the first run with warmed runs.
            let (work, total) = std::thread::spawn(move || {
                let length = if grow_chain { size } else { 8 };
                let (context, goal) = chain(length, size * 4);
                let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
                    connected_condition_premises(&context, &goal, false).unwrap()
                });
                assert_eq!(selected.len(), length);
                assert!(
                    work >= length && work <= 16 * (length + size * 4),
                    "{length}: {work}"
                );
                let (proof, total) = crate::instrumentation::measure_deterministic_work(|| {
                    crate::kernel::search::ProofSearch::derive_atomic_proposition(&(context), &goal)
                        .expect("connected order chain proves goal")
                });
                assert!(proof.check(&context));
                assert_eq!(proof.context_premises().len(), length);
                eprintln!(
                    "chain {length}, unrelated {}: selection {work}, complete {total}",
                    size * 4
                );
                // Every link is necessary: a chain without it neither checks
                // the certificate nor proves the goal.
                for index in 1..=length as u64 {
                    let weakened = (1..=length as u64)
                        .filter(|link| *link != index)
                        .fold(PureFactContext::new(), |weakened, link| {
                            weakened.assume_condition(chain_fact(link), true)
                        });
                    assert!(!proof.check(&weakened));
                    if index == length as u64 / 2 {
                        assert!(
                            crate::kernel::search::ProofSearch::derive_atomic_proposition(
                                &weakened, &goal
                            )
                            .is_none()
                        );
                    }
                }
                (work, total)
            })
            .join()
            .expect("condition scaling sample");
            samples.push(work);
            complete.push(total);
        }
        if !grow_chain {
            assert!(
                samples.iter().all(|work| *work == samples[0]),
                "{samples:?}"
            );
            assert!(
                complete.iter().all(|work| *work == complete[0]),
                "{complete:?}"
            );
        }
        for curve in [&samples, &complete] {
            for pair in curve.windows(2) {
                assert!(pair[1] <= pair[0] * 3, "{curve:?}");
            }
        }
    }
}

#[test]
fn covering_loadability_avoids_unrelated_adjacency_search() {
    let mut samples = Vec::new();
    for size in [8, 32, 128] {
        let memory = Memory::new();
        // The theorem frontend represents these pointers in one block, so
        // unrelated ranges remain candidates for the adjacency search.
        let pointer = |index| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(term(index), 4),
        };
        let source = Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: pointer(1),
            bytes: 16.into(),
            wide: false,
        };
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_proposition(Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: pointer(100 + index),
                bytes: 16.into(),
                wide: false,
            });
            context = context.assume_condition(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(term(10_000 + index)),
                    right: Box::new(1000.into()),
                },
                true,
            );
        }
        context = context.assume_proposition(source.clone());
        let goal = Proposition::MemoryLoadable {
            memory,
            base: pointer(1).offset_by_bytes(4),
            bytes: 4.into(),
            wide: false,
        };
        let (proof, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::search::ProofSearch::derive_solve_atomic_proposition(&(context), &goal)
                .unwrap()
        });
        assert_eq!(proof.context_premises(), vec![source]);
        samples.push(work);
    }
    assert!(
        samples[2].saturating_sub(samples[1]) <= 5 * samples[1].saturating_sub(samples[0]) + 64,
        "covering loadability must scale linearly: {samples:?}"
    );
    eprintln!("covering loadability work: {samples:?}");
}

#[test]
fn arithmetic_candidates_omit_registered_read_definitions() {
    let mut samples = Vec::new();
    for size in [4, 16, 64] {
        let memory = intern_memory(Memory::new().with_block("buffer", 4096));
        let mut context = PureFactContext::new();
        let mut reads = Vec::new();
        for index in 0..size {
            let read = MachineTerm::MemoryLoad(
                memory.clone(),
                Box::new(Pointer {
                    block: "buffer".into(),
                    offset: PointerOffsetTerm::Constant(index * 4),
                }),
                LoadKind::Int32,
            );
            let (variable, load) = load_variable_for_term(&read).unwrap();
            context = context.assume_condition(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(MachineTerm::Variable(variable)),
                    right: Box::new(load.clone()),
                },
                true,
            );
            reads.push((variable, load));
        }
        // An equation between different reads is useful, even when its left
        // operand is a reserved load name. It must remain a candidate.
        let alias = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(reads[0].0)),
                right: Box::new(reads[1].1.clone()),
            },
            true,
        );
        context = context.assume_proposition(alias.clone());
        let sum = reads.iter().fold(0.into(), |sum, (variable, _)| {
            binary_node!(
                Int32,
                Add,
                Box::new(sum),
                Box::new(MachineTerm::Variable(*variable)),
            )
        });
        let goal = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(sum),
                right: Box::new(7.into()),
            },
            true,
        );
        let ((equalities, premises), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                (
                    connected_equalities(&context, &goal).unwrap(),
                    arithmetic_connected_premises(&context, &goal).unwrap(),
                )
            });
        assert_eq!(equalities, vec![alias.clone()]);
        assert_eq!(premises, vec![alias]);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 5 * pair[0]),
        "{samples:?}"
    );
    eprintln!("registered read candidate work: {samples:?}");
}
