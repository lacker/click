// Scaling tests of `src/kernel/proof/equality_rewrite.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::CompareRelation;

#[test]
fn pointer_rewrite_integer_reads_preserves_state_kind_and_scales() {
    for same_block in [false, true] {
        let mut samples = Vec::new();
        for size in [4u64, 16, 64, 256] {
            let _session = VerificationSession::enter();
            let mut p = Address::symbolic(Variable(241_000));
            let mut q = Address::symbolic(Variable(241_001)).offset_by_bytes(3);
            if same_block {
                p.offset = AddressOffset::scale_int32(MachineTerm::Variable(Variable(241_002)), 1);
                q.base = p.base.clone();
                q.offset = AddressOffset::scale_int32(MachineTerm::Variable(Variable(241_003)), 1);
            }
            let cited =
                Proposition::condition_is(ConditionTerm::address_equal(p.clone(), q.clone()), true);
            let mut memory = SymbolicMemory::new();
            let mut facts = PureFactStore::default().with_fact(cited.clone());
            for index in 0..size {
                memory = memory.store(
                    Address::symbolic(Variable(242_000 + index)),
                    crate::kernel::uint8(7),
                );
                facts = facts.with_fact(integer_equality(
                    IntegerTerm::var(Variable(244_000 + index)),
                    IntegerTerm::constant_i64(index as i64),
                ));
            }
            let read = |memory: &SymbolicMemory, pointer: &Address, kind| {
                MachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
                    &crate::kernel::intern_memory(memory.clone()),
                    pointer,
                    kind,
                    1,
                ))
            };
            // The read identity preserves only its original cell. The observed
            // origin is needed when the equality exposes the alias address.
            let source = MachineTerm::Variable(crate::kernel::load_variable_for_cell_with_origin(
                &crate::kernel::intern_memory(SymbolicMemory::new()),
                &p,
                LoadKind::UInt8,
                1,
                &crate::kernel::intern_memory(memory.clone()),
            ));
            let target = read(&memory, &q, LoadKind::UInt8);
            let later = memory.clone().store(q.clone(), crate::kernel::uint8(99));
            let other_memory_state = read(&later, &q, LoadKind::UInt8);
            let other_kind = read(&memory, &q, LoadKind::Int8);
            let mut work = 0;
            for ty in [
                MachineIntegerType::Int32,
                MachineIntegerType::UInt32,
                MachineIntegerType::Int64,
                MachineIntegerType::UInt64,
            ] {
                // A 32-bit observation of a byte load is the byte's own.
                let observation = |value| IntegerTerm::from_machine(ty, value).unwrap();
                // The rewritten goal states its comparison of an observation
                // and a constant in the one form, the native comparison.
                let observed_zero = |value| {
                    crate::kernel::assumptions::canonical_observation_form(&integer_equality(
                        observation(value),
                        IntegerTerm::constant_i64(0),
                    ))
                };
                let goal =
                    integer_equality(observation(source.clone()), IntegerTerm::constant_i64(0));
                let expected = observed_zero(target.clone());
                let (checked, cost) = crate::instrumentation::measure_deterministic_work(|| {
                    facts.check_equality_rewrite(&goal, &cited)
                });
                let checked = checked.unwrap();
                assert_eq!(checked.proposition(), &expected);
                assert_ne!(
                    checked.proposition(),
                    &observed_zero(other_memory_state.clone())
                );
                assert_ne!(checked.proposition(), &observed_zero(other_kind.clone()));
                assert!(
                    PureFactStore::default()
                        .check_equality_rewrite(&goal, &cited)
                        .is_err()
                );
                work += cost;
            }
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "{samples:?}"
        );
    }
}

/// Rewriting a field owner changes a typed read's address, not the
/// loaded value's legacy storage-relative offset. Exercise cold reads
/// with growing unrelated states and premises, plus ordinary indexing.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn pointer_read_rewrite_preserves_value_state_and_scales() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = Address::symbolic(Variable(211_000));
        let alias = Address {
            base: AddressBase::Symbolic(Variable(211_001)),
            offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(211_002)), 4),
        };
        let address = owner.offset_by_bytes(16);
        let alias_address = alias.offset_by_bytes(16);
        let cited = Proposition::condition_is(
            ConditionTerm::address_equal(owner.clone(), alias.clone()),
            true,
        );
        let mut facts = PureFactStore::default().with_fact(cited.clone());
        let mut memory = SymbolicMemory::new();
        for i in 0..size {
            memory = memory.store(
                Address::symbolic(Variable(220_000 + i)),
                ProgramValue::Int32(MachineTerm::constant(7)),
            );
            facts = facts.with_fact(equality(
                MachineTerm::Variable(Variable(230_000 + i)),
                MachineTerm::constant(i as u32),
            ));
        }
        let context = PureFactContext::new();
        let read = |memory: &SymbolicMemory, address: &Address| {
            let paths = crate::kernel::eval::evaluate_logical_memory_load_paths(
                memory,
                address.clone(),
                ProgramType::Int32Pointer,
                Default::default(),
                Vec::new(),
                &context,
            );
            let [path] = paths.as_slice() else {
                panic!("one logical read");
            };
            assert!(!path.facts.has_path_conditions() && path.obligations.is_empty());
            let crate::kernel::ExpressionOutcome::Value(ProgramValue::Pointer(value)) =
                &path.outcome
            else {
                panic!("typed pointer read");
            };
            value.address().clone()
        };
        let original = read(&memory, &address);
        let leaf = Address::symbolic(Variable(211_003));
        let goal = Proposition::condition_is(
            ConditionTerm::address_equal(original.clone(), leaf.clone()),
            true,
        );
        assert!(
            PureFactStore::default()
                .check_equality_rewrite(&goal, &cited)
                .is_err()
        );
        let ((rewritten, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                facts.check_equality_rewrite(&goal, &cited).unwrap()
            })
        });
        let Some((ConditionTerm::AddressEqual(actual, rhs), true)) =
            rewritten.proposition().condition_native()
        else {
            panic!("full pointer equality retained");
        };
        assert_eq!(rhs.as_ref(), &leaf);
        assert_eq!(actual.offset, AddressOffset::Constant(0));
        let expected = read(&memory, &alias_address);
        assert!(context.pointers_known_equal(actual, &expected));
        assert!(!ResourceContext::new().permits_memory_read(&alias_address, 8, &context));
        let replacement = Address::symbolic(Variable(211_004));
        let later = memory.clone().store(
            alias_address.clone(),
            ProgramValue::typed_pointer(replacement.clone(), ProgramType::Int32Pointer),
        );
        assert_eq!(read(&later, &alias_address), replacement);
        assert!(!context.pointers_known_equal(actual, &replacement));
        // A read created after the store must rewrite to the new pointer,
        // while the previously rewritten read above retains its state.
        let stored_goal = Proposition::condition_is(
            ConditionTerm::address_equal(read(&later, &address), replacement.clone()),
            true,
        );
        let stored_rewrite = facts.check_equality_rewrite(&stored_goal, &cited).unwrap();
        assert_eq!(
            stored_rewrite.proposition(),
            &Proposition::condition_is(
                ConditionTerm::address_equal(replacement.clone(), replacement),
                true,
            )
        );
        // An unregistered scaled integer is still pointer arithmetic.
        let index = MachineTerm::Variable(Variable(211_005));
        let indexed = Address::loaded(&index.clone()).unwrap();
        let arithmetic_goal =
            Proposition::condition_is(ConditionTerm::address_equal(indexed, leaf.clone()), true);
        let arithmetic = facts
            .check_equality_rewrite(&arithmetic_goal, &cited)
            .unwrap();
        let expected_indexed = alias.offset_by_int32_elements(index);
        assert_eq!(
            arithmetic.proposition(),
            &Proposition::condition_is(ConditionTerm::address_equal(expected_indexed, leaf), true,)
        );
        samples.push((work, map_work));
    }
    assert!(
        samples.iter().all(|sample| sample.0 <= samples[0].0 + 128),
        "{samples:?}"
    );
    assert!(
        samples.iter().all(|sample| sample.1 <= samples[0].1 + 1024),
        "{samples:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn native_equality_rewrite_preserves_wide_order_and_truth_value() {
    let x = MachineTerm::Variable(Variable(193_020));
    let y = MachineTerm::Variable(Variable(193_021));
    let cited = Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(x.clone()),
            right: Box::new(y.clone()),
        },
        true,
    );
    // The same immutable ambient sets exercise every order/truth case.
    // Build them once so fixture setup does not dominate this gate test.
    let fact_sets: Vec<_> = [0, 16, 64, 256, 1024]
        .into_iter()
        .map(|ambient| {
            let mut facts = PureFactStore::default().with_fact(cited.clone());
            for i in 0..ambient {
                facts = facts.with_fact(equality(
                    MachineTerm::Variable(Variable(194_000 + i)),
                    MachineTerm::constant(i as u32),
                ));
            }
            facts
        })
        .collect();
    let comparisons = [MachineIntegerType::Int64, MachineIntegerType::UInt64]
        .into_iter()
        .flat_map(|format| {
            [
                CompareRelation::LessThan,
                CompareRelation::LessEqual,
                CompareRelation::GreaterThan,
                CompareRelation::GreaterEqual,
            ]
            .map(move |relation| {
                move |left, right| ConditionTerm::Compare {
                    format,
                    relation,
                    left,
                    right,
                }
            })
        });
    for make in comparisons {
        for bound in [
            MachineTerm::int64_constant(i64::MIN),
            MachineTerm::uint64_constant(u64::MAX),
        ] {
            for truth in [false, true] {
                let goal = Proposition::condition_is(
                    make(Box::new(x.clone()), Box::new(bound.clone())),
                    truth,
                );
                let expected = Proposition::condition_is(
                    make(Box::new(y.clone()), Box::new(bound.clone())),
                    truth,
                );
                assert!(
                    PureFactStore::default()
                        .check_equality_rewrite(&goal, &cited)
                        .is_err()
                );
                let mut costs = Vec::new();
                for facts in &fact_sets {
                    let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                        facts.check_equality_rewrite(&goal, &cited)
                    });
                    let mut checked = result.unwrap();
                    assert_eq!(checked.proposition(), &expected);
                    let forged = Proposition::condition_is(
                        make(Box::new(y.clone()), Box::new(bound.clone())),
                        !truth,
                    );
                    assert!(!checked.try_present_as(&forged));
                    assert_eq!(checked.proposition(), &expected);
                    costs.push(work);
                }
                assert!(
                    costs[0] > 0 && costs.iter().all(|cost| *cost == costs[0]),
                    "{costs:?}"
                );
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.9s in the parallel gate"]
fn native_integer_bound_rewrite_is_dag_linear_and_budget_checked() {
    let x = MachineTerm::Variable(Variable(193_028));
    let y = MachineTerm::Variable(Variable(193_029));
    let cited = equality(x.clone(), y.clone());
    let make_term = |value, depth| {
        let mut term: SharedIntegerTerm =
            IntegerTerm::from_machine(MachineIntegerType::UInt32, value)
                .unwrap()
                .into();
        for _ in 0..depth {
            term = IntegerTerm::add(term.as_ref().clone(), term.as_ref().clone()).into();
        }
        term
    };
    let condition = |term| {
        Proposition::condition_is(
            ConditionTerm::IntegerLessEqual(term, IntegerTerm::constant_i64(4294967295).into()),
            true,
        )
    };
    let mut depth_costs = Vec::new();
    for depth in [4, 8, 16, 32] {
        let goal = condition(make_term(x.clone(), depth));
        let expected = condition(make_term(y.clone(), depth));
        let mut ambient_costs = Vec::new();
        for ambient in [0, 16, 64, 256, 1024] {
            let mut facts = PureFactStore::default().with_fact(cited.clone());
            for i in 0..ambient {
                facts = facts.with_fact(equality(
                    MachineTerm::Variable(Variable(195_000 + i)),
                    MachineTerm::constant(i as u32),
                ));
            }
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.check_equality_rewrite(&goal, &cited)
            });
            assert_eq!(result.unwrap().proposition(), &expected);
            ambient_costs.push(work);
        }
        assert!(
            ambient_costs[0] > 0 && ambient_costs.iter().all(|cost| *cost == ambient_costs[0]),
            "{ambient_costs:?}"
        );
        depth_costs.push(ambient_costs[0]);
    }
    assert!(depth_costs[3] <= depth_costs[0] * 10, "{depth_costs:?}");
    let facts = PureFactStore::default().with_fact(cited.clone());
    let result = crate::instrumentation::with_run_work_limit(0, || {
        facts.check_equality_rewrite(&condition(make_term(x, 32)), &cited)
    });
    assert!(
        result.is_err(),
        "an exhausted rewrite must not emit a partial refinement"
    );
}

#[test]
fn integer_equality_rewrite_scales_with_selected_dag_not_ambient_facts() {
    let x = IntegerTerm::var(Variable(193_021));
    let y = IntegerTerm::var(Variable(193_022));
    let cited = integer_equality(x.clone(), y.clone());
    let mut costs = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let mut facts = PureFactStore::default().with_fact(cited.clone());
        for i in 0..size {
            facts = facts.with_fact(integer_equality(
                IntegerTerm::var(Variable(194_000 + i as u64)),
                IntegerTerm::constant_i64(i as i64),
            ));
        }
        let small = integer_equality(IntegerTerm::multiply(x.clone(), x.clone()), y.clone());
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&small, &cited)
        });
        checked.unwrap();
        costs.push(work);
        // Repeated squaring has exponentially many paths but a linear DAG.
        let mut term: SharedIntegerTerm = x.clone().into();
        for _ in 0..size {
            term = IntegerTerm::Multiply(term.clone(), term).into();
        }
        let goal = integer_equality(term.as_ref().clone(), y.clone());
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&goal, &cited)
        });
        let checked = checked.unwrap();
        assert!(work <= 20 * size + 100, "size {size}: {work}");
        let Some((ConditionTerm::IntegerEqual(root, _), true)) =
            checked.proposition().condition_native()
        else {
            unreachable!()
        };
        let mut root = root.clone();
        for _ in 0..size {
            let IntegerTerm::Multiply(a, b) = root.as_ref() else {
                unreachable!()
            };
            assert_eq!(a.id(), b.id());
            root = a.clone();
        }
        assert_eq!(root.as_ref(), &y);
    }
    assert!(costs.iter().all(|work| *work == costs[0]), "{costs:?}");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn cited_read_rewrite_requires_unchanged_cells_and_its_named_premise() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Address {
        base: "rewrite-selected-read".into(),
        offset: AddressOffset::Constant(0),
    };
    crate::kernel::eval::declare_load_access_width(&pointer, 4);
    let before = SymbolicMemory::new().with_block("rewrite-selected-read", 4);
    let after = before.clone().with_block("local:rewrite-unrelated", 4);
    let changed = after.clone().store(
        pointer.clone(),
        ProgramValue::Int32(MachineTerm::constant(43)),
    );
    let load = |memory: &SymbolicMemory| {
        MachineTerm::read_named(
            ProgramPoint::at(&(crate::kernel::intern_memory_ref(memory))),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Int32,
        )
    };
    let premise = equality(load(&before), MachineTerm::constant(42));
    let goal = equality(load(&after), MachineTerm::constant(42));
    let mut costs = vec![];
    for size in [16u64, 64, 256, 1024] {
        let mut facts = PureFactStore::from_ordered(std::slice::from_ref(&premise));
        for index in 0..size {
            facts = facts.with_fact(equality(
                MachineTerm::Variable(Variable(80_000 + index)),
                MachineTerm::constant(index as u32),
            ));
        }
        crate::kernel::eval::clear_load_canonicalization_caches();
        let (rewritten, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&goal, &premise)
        });
        assert_eq!(
            rewritten.unwrap().proposition(),
            &Proposition::condition_is(ConditionTerm::Constant(true), true)
        );
        assert!(
            facts
                .check_equality_rewrite(
                    &equality(load(&changed), MachineTerm::constant(42)),
                    &premise
                )
                .is_err()
        );
        costs.push(work);
    }
    assert!(costs.iter().all(|work| *work <= 8), "{costs:?}");
    assert!(
        PureFactStore::default()
            .check_equality_rewrite(&goal, &premise)
            .is_err()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn same_block_pointer_view_rewrite_preserves_span_and_selected_work() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = AddressOffset::scale_int32(MachineTerm::Variable(Variable(192_920)), 1);
    let target = AddressOffset::scale_int32(MachineTerm::Variable(Variable(192_921)), 1);
    let cited = Proposition::condition_is(
        ConditionTerm::AddressOffsetEqual(Box::new(source.clone()), Box::new(target.clone())),
        true,
    );
    let memory = SymbolicMemory::new().with_block("offset-view-rewrite", 8);
    let span = MachineTerm::Variable(Variable(192_922));
    let goal = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: Address {
            base: AddressBase::ExternalArgument,
            offset: AddressOffset::add(source, AddressOffset::Constant(2)),
        },
        bytes: (span.clone()).into(),
        wide: false,
    };
    assert!(
        PureFactStore::default()
            .check_equality_rewrite(&goal, &cited)
            .is_err()
    );
    let false_equality = match &cited {
        Proposition::ConditionIs(condition, _) => {
            Proposition::condition_is(condition.clone(), false)
        }
        _ => unreachable!(),
    };
    let false_facts = PureFactStore::from_ordered(&[false_equality]);
    assert!(false_facts.check_equality_rewrite(&goal, &cited).is_err());
    let mut costs = Vec::new();
    for size in [0, 16, 64, 256, 1024] {
        let mut facts = PureFactStore::from_ordered(std::slice::from_ref(&cited));
        for index in 0..size {
            facts = facts.with_fact(equality(
                MachineTerm::Variable(Variable(210_000 + index)),
                MachineTerm::constant(index as u32),
            ));
        }
        let (rewritten, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&goal, &cited).unwrap()
        });
        let Proposition::MemoryLoadable {
            memory: retained_state,
            base,
            bytes,
            ..
        } = rewritten.proposition()
        else {
            panic!("viewability changed kind")
        };
        assert_eq!(
            retained_state.diagnostic_identity(),
            memory.diagnostic_identity()
        );
        assert_eq!(base.base, AddressBase::ExternalArgument);
        assert_eq!(
            base.offset,
            AddressOffset::add(target.clone(), AddressOffset::Constant(2))
        );
        assert_eq!(bytes.native_compat(), &span);
        costs.push(work);
    }
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

#[test]
fn pointer_view_rewrite_preserves_state_span_and_ambient_scaling() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Address::symbolic(Variable(192_910));
    let target = Address::symbolic(Variable(192_911));
    let cited = Proposition::condition_is(
        ConditionTerm::address_equal(source.clone(), target.clone()),
        true,
    );
    let memory = SymbolicMemory::new().with_block("pointer-view-rewrite", 8);
    let span = MachineTerm::Variable(Variable(192_912));
    let goal = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: source,
        bytes: (span.clone()).into(),
        wide: false,
    };
    assert!(
        PureFactStore::default()
            .check_equality_rewrite(&goal, &cited)
            .is_err()
    );
    let mut costs = Vec::new();
    for size in [0, 4, 16, 64, 256] {
        let mut facts = PureFactStore::from_ordered(std::slice::from_ref(&cited));
        for index in 0..size {
            facts = facts.with_fact(equality(
                MachineTerm::Variable(Variable(200_000 + index)),
                MachineTerm::constant(index as u32),
            ));
        }
        let (rewritten, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&goal, &cited).unwrap()
        });
        let Proposition::MemoryLoadable {
            memory: retained_state,
            base,
            bytes,
            wide: false,
        } = rewritten.proposition()
        else {
            panic!("viewability changed kind")
        };
        assert_eq!(
            retained_state.diagnostic_identity(),
            memory.diagnostic_identity()
        );
        assert_eq!(base, &target);
        assert_eq!(bytes.native_compat(), &span);
        costs.push(work);
    }
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

#[test]
fn pointer_rewrite_enters_scalar_calls_and_preserves_scope_and_states() {
    let variable = Variable(920);
    let source = Address::symbolic(variable);
    let target = Address::symbolic(Variable(921));
    let cited = Proposition::condition_is(
        ConditionTerm::PointerEqual(
            Box::new(Pointer::new(source.clone(), ProgramType::Int32Pointer)),
            Box::new(Pointer::new(target.clone(), ProgramType::Int32Pointer)),
        ),
        true,
    );
    let memory = SymbolicMemory::new().with_block("unchanged", 4);
    let goal_at = |pointer: Address, count: usize| {
        equality(
            MachineTerm::ClickFunctionApplication {
                name: "observes".into(),
                arguments: vec![
                    PureFunctionArgument::ArrayRef {
                        point: crate::kernel::ProgramPoint::of_memory(&memory),
                        pointer: ProgramValue::typed_pointer(pointer, ProgramType::Int32Pointer),
                        element_type: ProgramType::Int32,
                    };
                    count
                ],
            },
            MachineTerm::constant(1),
        )
    };
    let facts = PureFactStore::from_ordered(std::slice::from_ref(&cited));
    let goal = goal_at(source.clone(), 1);
    assert_eq!(
        facts
            .check_equality_rewrite(&goal, &cited)
            .unwrap()
            .proposition(),
        &goal_at(target.clone(), 1)
    );
    assert!(
        PureFactStore::default()
            .check_equality_rewrite(&goal, &cited)
            .is_err()
    );
    // Quantifying the source binds every occurrence the equality could
    // rewrite; quantifying the target binds it as the quantifier's own bound
    // variable, so the rewritten target stays free.
    for (bound, rewrites) in [(variable, false), (Variable(921), true)] {
        let quantified = crate::kernel::quantifiers::test_forall(
            Default::default(),
            bound,
            Sort::ProgramPointer(ProgramType::Int32Pointer),
            goal.clone(),
        );
        assert_eq!(
            facts.check_equality_rewrite(&quantified, &cited).is_ok(),
            rewrites,
            "the equality rewrites only a free source"
        );
    }
    let displaced = Proposition::condition_is(
        ConditionTerm::address_equal(
            Address {
                base: source.base.clone(),
                offset: AddressOffset::Constant(4),
            },
            target.clone(),
        ),
        true,
    );
    assert!(
        PureFactStore::from_ordered(std::slice::from_ref(&displaced))
            .check_equality_rewrite(&goal, &displaced)
            .is_err(),
        "equality at an offset does not identify the whole pointer"
    );
    let costs = [16, 32, 64, 128].map(|size| {
        let goal = goal_at(source.clone(), size);
        let (checked, cost) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&goal, &cited).unwrap()
        });
        assert_eq!(checked.proposition(), &goal_at(target.clone(), size));
        cost
    });
    assert!(costs[0] > 0);
    assert!(
        costs.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 8),
        "scalar-call rewrite rescanned its argument list: {costs:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn checked_rewrite_does_not_scan_or_rebuild_ambient_facts() {
    let x = MachineTerm::Variable(Variable(921));
    let cited = equality(x.clone(), MachineTerm::constant(7));
    let goal = equality(x, MachineTerm::constant(9));
    let mut costs = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut facts = PureFactStore::default();
        for index in 0..size {
            facts = facts.with_fact(equality(
                MachineTerm::Variable(Variable(10_000 + index)),
                MachineTerm::constant(index as u32),
            ));
        }
        facts = facts.with_fact(cited.clone());
        super::super::super::take_fact_entry_counts();
        let (_, cost) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&goal, &cited).unwrap()
        });
        assert_eq!(super::super::super::take_fact_entry_counts(), (0, 0));
        costs.push(cost);
    }
    assert!(costs[0] > 0);
    assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
}

#[test]
fn rewrite_capture_collection_does_not_visit_state_contents() {
    let free = Variable(41);
    let address = Variable(42);
    let mut costs = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut memory = SymbolicMemory::new();
        for i in 0..size {
            memory = memory.store(
                Address::symbolic(Variable(100_000 + i)),
                ProgramValue::Int32(MachineTerm::Variable(Variable(200_000 + i))),
            );
        }
        let equality = Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(free)),
                right: Box::new(MachineTerm::read_named(
                    ProgramPoint::at(&(crate::kernel::intern_memory(memory))),
                    Box::new(Address::symbolic(address)),
                    crate::kernel::LoadKind::Int32,
                )),
            },
            true,
        );
        let (variables, work) = crate::instrumentation::measure_deterministic_work(|| {
            rewrite_equality_variables(&equality).unwrap()
        });
        assert_eq!(variables, BTreeSet::from([free, address]));
        costs.push(work);
    }
    assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
}

#[test]
fn rewrite_integer_application_endpoint_keeps_byte_state_and_ignores_its_contents() {
    let index = MachineTerm::Variable(Variable(47));
    let replacement = MachineTerm::constant(9);
    let equality = Proposition::condition_is(
        ConditionTerm::equal(index.clone(), replacement.clone()),
        true,
    );
    let mut costs = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut memory = SymbolicMemory::new();
        for i in 0..size {
            memory = memory.store(
                Address::symbolic(Variable(300000 + i)),
                ProgramValue::Int32(MachineTerm::constant(i as u32)),
            );
        }
        let array = PureFunctionArgument::ArrayRef {
            point: crate::kernel::ProgramPoint::of_memory(&memory),
            pointer: ProgramValue::typed_pointer(
                Address::symbolic(Variable(48)),
                ProgramType::UInt8Pointer,
            ),
            element_type: ProgramType::UInt8,
        };
        let application = |endpoint| {
            IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                "prefix".into(),
                vec![
                    array.clone(),
                    PureFunctionArgument::Value(ProgramValue::Int32(endpoint)),
                ],
            ))
        };
        let goal = Proposition::condition_is(
            ConditionTerm::integer_equal(
                application(index.clone()),
                application(replacement.clone()),
            ),
            true,
        );
        let expected = Proposition::condition_is(
            ConditionTerm::integer_equal(
                application(replacement.clone()),
                application(replacement.clone()),
            ),
            true,
        );
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&equality));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts
                .check_equality_rewrite(&goal, &equality)
                .map(|checked| checked.proposition().clone())
        });
        assert_eq!(result.unwrap(), expected);
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work == costs[0]),
        "{costs:?}"
    );
}

#[test]
fn checked_integer_rewrite_is_exact_and_ignores_unrelated_facts() {
    let x: SharedIntegerTerm = IntegerTerm::var(Variable(187_001)).into();
    let y: SharedIntegerTerm = IntegerTerm::var(Variable(187_002)).into();
    let eq = |a, b| Proposition::condition_is(ConditionTerm::IntegerEqual(a, b), true);
    let cited = eq(x.clone(), y.clone());
    let goal = eq(
        IntegerTerm::TruncatingQuotient(x.clone(), IntegerTerm::constant_i64(2).into()).into(),
        y.clone(),
    );
    let expected = eq(
        IntegerTerm::TruncatingQuotient(y.clone(), IntegerTerm::constant_i64(2).into()).into(),
        y.clone(),
    );
    assert!(
        PureFactStore::default()
            .check_equality_rewrite(&goal, &cited)
            .is_err()
    );
    let mut costs = Vec::new();
    for size in [4u64, 16, 64, 256] {
        let mut facts = PureFactStore::default();
        for index in 0..size {
            facts = facts.with_fact(eq(
                IntegerTerm::var(Variable(188_000 + index)).into(),
                IntegerTerm::constant_i64(index as i64).into(),
            ));
        }
        // Admission may use the reversed exact fact; rewriting follows the cited direction.
        facts = facts.with_fact(eq(y.clone(), x.clone()));
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&goal, &cited)
        });
        assert_eq!(checked.unwrap().proposition(), &expected);
        costs.push(work);
        assert!(
            facts
                .check_equality_rewrite(&goal, &eq(x.clone(), IntegerTerm::constant_i64(42).into()))
                .is_err()
        );
    }
    assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
    let captured = crate::kernel::quantifiers::test_forall(
        Default::default(),
        Variable(187_001),
        Sort::Integer,
        goal.clone(),
    );
    assert!(
        PureFactStore::default()
            .with_fact(cited.clone())
            .check_equality_rewrite(&captured, &cited)
            .is_err()
    );
    let mut false_equality = cited.clone();
    if let Proposition::ConditionIs(_, truth) = &mut false_equality {
        *truth = false;
    }
    assert!(
        PureFactStore::default()
            .with_fact(false_equality.clone())
            .check_equality_rewrite(&goal, &false_equality)
            .is_err()
    );
}

#[test]
fn integer_observation_rewrite_work_tracks_selected_comparison_leaves() {
    let word = MachineTerm::Variable(Variable(74_201));
    let source: SharedIntegerTerm =
        IntegerTerm::from_machine(MachineIntegerType::UInt64, word.clone())
            .unwrap()
            .into();
    let target: SharedIntegerTerm = IntegerTerm::var(Variable(74_202)).into();
    let cited =
        Proposition::condition_is(ConditionTerm::IntegerEqual(source, target.clone()), true);
    let leaf = Proposition::condition_is(
        observed_native_condition(
            MachineIntegerType::UInt64,
            1,
            word,
            observed_native_bound(MachineIntegerType::UInt64),
        ),
        true,
    );
    let samples = [8usize, 16, 32, 64].map(|size| {
        let mut goal = leaf.clone();
        for _ in 1..size {
            goal = Proposition::And(Box::new(goal), Box::new(leaf.clone()));
        }
        let (rewritten, work) = crate::instrumentation::measure_deterministic_work(|| {
            rewrite_with_admitted_equality(&goal, &cited).unwrap()
        });
        let mut pending = vec![&rewritten];
        let mut leaves = 0;
        while let Some(proposition) = pending.pop() {
            match proposition {
                Proposition::And(left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
                condition_source_0 @ Proposition::ConditionIs(_, true)
                    if let Some((ConditionTerm::IntegerLessEqual(left, right), _)) =
                        condition_source_0.condition_native() =>
                {
                    assert_eq!(left, &target);
                    assert_eq!(right.as_ref(), &IntegerTerm::constant_i64(10));
                    leaves += 1;
                }
                _ => panic!("a selected native comparison lost its observed rewrite"),
            }
        }
        assert_eq!(leaves, size);
        assert!(work <= 128 * size + 256, "{size}: {work} work");
        work
    });
    for pair in samples.windows(2) {
        assert!(
            pair[1] > pair[0] && pair[1] <= 2 * pair[0] + 32,
            "{samples:?}"
        );
    }
}

fn pointer_read_chain_rewrite_work(
    depth: usize,
    repeats: usize,
    cells: u64,
    native: bool,
    hit: bool,
) -> usize {
    let _session = VerificationSession::enter();
    let from = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(998_950)), 8),
    };
    let to = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(998_951)), 8),
    };
    let mut memory = SymbolicMemory::new();
    for index in 0..cells {
        memory = memory.store(
            Address {
                base: AddressBase::Temporary(999_000 + index),
                offset: AddressOffset::Constant(0),
            },
            ProgramValue::Int32(7u32.into()),
        );
    }
    let memory = crate::kernel::intern_memory(memory);
    let read = |address: &Address| {
        if native {
            Address::version_read(&memory, address)
        } else {
            let term = MachineTerm::read_named(
                ProgramPoint::at(&memory),
                Box::new(address.clone()),
                LoadKind::Int32,
            );
            let (variable, _) =
                crate::kernel::load_variable_for_term(&term).expect("legacy read adapter");
            Address::symbolic(variable)
        }
    };
    let mut input = from.clone();
    for _ in 0..depth {
        input = read(&input);
    }
    let rewrite = |address: &Address| {
        if hit && address == &from {
            to.clone()
        } else {
            address.clone()
        }
    };
    let (outputs, work) = crate::instrumentation::measure_deterministic_work(|| {
        let cache = PointerReadRewrites::default();
        (0..repeats)
            .map(|index| {
                rewrite_through_loaded_address_base(
                    &input.clone().offset_by_bytes(index as u32),
                    &rewrite,
                    &cache,
                )
            })
            .collect::<Vec<_>>()
    });
    if hit {
        let mut expected = to;
        for _ in 0..depth {
            expected = read(&expected);
        }
        for (index, output) in outputs.into_iter().enumerate() {
            assert_eq!(output, Some(expected.clone().offset_by_bytes(index as u32)));
        }
    } else {
        assert!(outputs.iter().all(Option::is_none));
    }
    work
}

#[test]
fn pointer_read_chain_rewrites_scale_with_selected_definitions() {
    for native in [false, true] {
        let samples = [8, 16, 32, 64]
            .map(|depth| pointer_read_chain_rewrite_work(depth, 1, 16, native, true));
        assert!(samples[0] > 0);
        assert!(
            samples
                .windows(3)
                .all(|p| p[2] - p[1] <= 2 * (p[1] - p[0]) + 8),
            "{native}: {samples:?}"
        );
    }
}

#[test]
fn pointer_read_chain_rewrites_share_hits_and_misses() {
    for native in [false, true] {
        for hit in [false, true] {
            let samples = [1, 4, 16, 64]
                .map(|repeats| pointer_read_chain_rewrite_work(64, repeats, 16, native, hit));
            assert!(samples[0] > 0);
            for (repeats, work) in [1, 4, 16, 64].into_iter().zip(samples) {
                assert!(
                    work <= samples[0] + 16 * repeats,
                    "native={native} hit={hit}: {samples:?}"
                );
            }
        }
    }
}

#[test]
fn pointer_read_chain_rewrites_ignore_surrounding_storage() {
    for native in [false, true] {
        // A nonempty state makes legacy reads register their definitions
        // in the naming graph; the empty state takes a cheaper path. Compare
        // nonempty sizes to isolate growth, without warming any target read.
        let samples = [1, 16, 64, 256]
            .map(|cells| pointer_read_chain_rewrite_work(16, 1, cells, native, true));
        assert!(samples[0] > 0);
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 64),
            "{native}: {samples:?}"
        );
    }
}

#[test]
fn machine_readings_of_selected_integer_facts_ignore_ambient_facts() {
    let mut samples = Vec::new();
    for size in [4u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let n = MachineTerm::Variable(Variable(249_000));
        let r = MachineTerm::Variable(Variable(249_001));
        let observe = |word| IntegerTerm::from_machine(ty, word).unwrap();
        let difference = IntegerTerm::subtract(observe(n.clone()), observe(r.clone()));
        let bound = Proposition::condition_is(
            ConditionTerm::integer_less_than(difference.clone(), observe(n.clone())),
            true,
        );
        let range =
            Proposition::condition_is(ConditionTerm::uint64_less_equal(r.clone(), n.clone()), true);
        let equality = integer_equality(difference, observe(n.clone()));
        let word = MachineTerm::uint64_subtract(n.clone(), r.clone());
        let goal =
            Proposition::condition_is(ConditionTerm::uint64_less_than(word, n.clone()), true);
        let mut facts = PureFactStore::default().with_fact(equality.clone());
        for index in 0..size {
            facts = facts.with_fact(Proposition::Predicate {
                name: format!("unrelated_machine_reading_{index}"),
                arguments: vec![],
            });
        }
        let no_range = facts.clone();
        let facts = facts.with_fact(range);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(no_range.shared_operation_reading(&bound).is_none());
                let Proposition::ConditionIs(condition, truth) = &goal else {
                    unreachable!()
                };
                let shared_goal = crate::kernel::machine_integer::comparison::comparison_view(
                    condition.native_compat(),
                    *truth,
                )
                .unwrap()
                .integer_condition();
                assert_eq!(
                    facts.shared_operation_reading(&bound),
                    Some(Proposition::condition_is(shared_goal, true))
                );
                let rewritten = facts.check_equality_rewrite(&goal, &equality).unwrap();
                assert_eq!(
                    rewritten.proposition(),
                    &Proposition::condition_is(
                        ConditionTerm::uint64_less_than(n.clone(), n.clone()),
                        true,
                    )
                );
                assert!(
                    PureFactStore::default()
                        .check_equality_rewrite(&goal, &equality)
                        .is_err()
                );
            })
        });
        samples.push((work, map_work));
    }
    assert!(
        samples[3].0 <= samples[0].0 * 2 + 32,
        "ambient scan: {samples:?}"
    );
    assert!(
        samples[3].1 <= samples[0].1 * 4 + 64,
        "ambient map scan: {samples:?}"
    );
}

#[test]
fn modular_integer_rewrite_work_tracks_the_cited_expression() {
    let mut samples = Vec::new();
    for depth in [2u64, 4, 8, 16] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let n = MachineTerm::Variable(Variable(250_000));
        let target = MachineTerm::Variable(Variable(250_001));
        let observe = |word| IntegerTerm::from_machine(ty, word).unwrap();
        let mut exact = observe(n.clone());
        let mut word = n.clone();
        for index in 0..depth {
            let operand = MachineTerm::Variable(Variable(251_000 + index));
            exact = IntegerTerm::subtract(exact, observe(operand.clone()));
            word = MachineTerm::uint64_subtract(word, operand);
        }
        let cited = integer_equality(exact, observe(target.clone()));
        let facts = PureFactStore::default().with_fact(cited.clone());
        let goal =
            Proposition::condition_is(ConditionTerm::uint64_less_than(word, n.clone()), true);
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&goal, &cited)
        });
        assert_eq!(
            checked.unwrap().proposition(),
            &Proposition::condition_is(ConditionTerm::uint64_less_than(target, n), true,)
        );
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3 + 64,
            "rewrite grew superlinearly: {samples:?}"
        );
    }
}

#[test]
fn shared_vacuous_sign_cast_equalities_only_inspect_roots() {
    let mut samples = Vec::new();
    for depth in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let signed = MachineIntegerType::Int32;
        let unsigned = MachineIntegerType::UInt32;
        let mut root = KernelTerm::variable(
            KernelType::Program(signed.program_type()),
            Variable(1007191),
        );
        for _ in 0..depth {
            root = KernelTerm::machine_binary_shared(
                signed,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let cast = KernelTerm::machine_cast_shared(
            MachineCastSpelling::Generic,
            signed,
            unsigned,
            root.clone(),
        );
        let observation = |ty, term: KernelTerm| {
            IntegerTerm::Machine(
                SharedMachineIntegerTerm::from_shared(ty, term.with_machine_observation_type(ty))
                    .unwrap(),
            )
        };
        let cast = observation(unsigned, cast);
        let word = observation(unsigned, root.clone());
        let signed_value = observation(signed, root);
        let forward = integer_equality(cast.clone(), word.clone());
        let reverse = integer_equality(word, cast.clone());
        let different_formats = integer_equality(cast, signed_value);
        let before = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(equality_is_vacuous(&forward));
            assert!(equality_is_vacuous(&reverse));
            assert!(!equality_is_vacuous(&different_formats));
        });
        assert_eq!(KernelTermExport::machine_export_count(), before);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn retained_pointer_index_rewrite_scales_with_distinct_nodes() {
    let mut costs = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let x = MachineTerm::Variable(Variable(1081301));
        let y = MachineTerm::Variable(Variable(1081302));
        let mut root = KernelTerm::retained_machine_operand(ty, MachineOperandView::Legacy(&x));
        for _ in 0..size {
            root =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [root.clone(), root]);
        }
        let index = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
        let pointer = Address {
            base: AddressBase::ExternalArgument,
            offset: AddressOffset::Int32Scaled {
                value: index.clone(),
                byte_width: 4,
            },
        };
        let goal = Proposition::condition_is(
            ConditionTerm::address_equal(pointer.clone(), Address::symbolic(Variable(1081303))),
            true,
        );
        let equality = Proposition::condition_is(ConditionTerm::equal(x, y.clone()), true);
        let facts = PureFactStore::default().with_fact(equality.clone());
        let exports = KernelTermExport::machine_export_count();
        let (rewritten, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&goal, &equality)
        });
        assert_ne!(rewritten.unwrap().proposition(), &goal);
        let (substituted, substitution_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::reasoning::substitute_bitvector_variable_in_pointer(
                    &pointer,
                    Variable(1081301),
                    &y,
                )
            });
        assert_ne!(substituted, pointer);
        assert!(!index.has_boxed_operand());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        costs.push(work + substitution_work);
    }
    assert!(costs[1] <= costs[0] * 5 + 100, "{costs:?}");
    assert!(costs[2] <= costs[1] * 5 + 100, "{costs:?}");
}

/// A reverse-direction rewrite used to rebuild every selected premise before
/// checking the explicitly available opposite orientation. Neither orientation,
/// including one selected from a conjunction, may reconstruct a fact context.
#[test]
fn selected_rewrite_premises_never_rebuild_a_context() {
    let eq = |a: u64, b: u64| {
        Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(Variable(a))),
                right: Box::new(MachineTerm::Variable(Variable(b))),
            },
            true,
        )
    };
    for n in [4_u64, 16, 64] {
        let _session = VerificationSession::enter();
        for conjunction in [false, true] {
            let mut available = (0..n)
                .map(|i| eq(100 + 2 * i, 101 + 2 * i))
                .collect::<Vec<_>>();
            let premise = eq(1, 2);
            available.push(if conjunction {
                Proposition::And(Box::new(premise), Box::new(eq(4, 5)))
            } else {
                premise
            });
            let before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
            for (from, to) in [(1, 2), (2, 1)] {
                let result =
                    rewrite_proposition_by_exact_equality(&eq(from, 3), &eq(from, to), &available)
                        .unwrap();
                assert_eq!(result, eq(to, 3));
            }
            assert!(
                rewrite_proposition_by_exact_equality(&eq(6, 3), &eq(6, 7), &available).is_err()
            );
            assert_eq!(
                crate::kernel::reasoning::path_facts::context_rebuild_entries() - before,
                0,
                "n={n}, conjunction={conjunction}: selected rewrite rebuilt its premise context"
            );
        }
    }
}

#[test]
fn selected_rewrite_does_not_discover_a_load_equality_chain() {
    let _session = VerificationSession::enter();
    let x = MachineTerm::Variable(Variable(800_001));
    let y = MachineTerm::Variable(Variable(800_002));
    let read = MachineTerm::read_named(
        ProgramPoint::at(&(intern_memory(SymbolicMemory::new()))),
        Box::new(Address::symbolic(Variable(800_003))),
        crate::kernel::LoadKind::Int32,
    );
    let eq = |a: MachineTerm, b: MachineTerm| {
        Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(a),
                right: Box::new(b),
            },
            true,
        )
    };
    let premises = [eq(x.clone(), read.clone()), eq(read.clone(), y.clone())];
    let goal = eq(x.clone(), MachineTerm::constant(9));
    assert!(rewrite_proposition_by_exact_equality(&goal, &eq(x, y.clone()), &premises).is_err());
    let first = rewrite_proposition_by_exact_equality(&goal, &premises[0], &premises).unwrap();
    let second = rewrite_proposition_by_exact_equality(&first, &premises[1], &premises).unwrap();
    assert_eq!(second, eq(y, MachineTerm::constant(9)));
}
