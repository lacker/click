// Scaling tests of `src/kernel/tests/external_array_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn external_array_unknown_snapshots_and_noop_maps_scale_with_representation() {
    let mut samples = Vec::new();
    for count in [8, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = external(930_000);
        let target = external(930_001);
        let before = CMemory::new();
        let (memory, work) = crate::instrumentation::measure_deterministic_work(|| {
            let memory = copy(before.clone(), &target, &source, count);
            let mut variables = std::collections::BTreeSet::new();
            crate::kernel::reasoning::collect_memory_bitvector_variables(&memory, &mut variables);
            assert!(variables.len() <= 8, "{variables:?}");
            assert!(variables.contains(&Variable(930_000)));
            assert!(variables.contains(&Variable(930_001)));
            let unchanged = crate::kernel::reasoning::substitute_bitvector_variable_in_memory(
                &memory,
                Variable(999_999),
                &17u32.into(),
            );
            assert_eq!(unchanged, memory);
            memory
        });
        assert_eq!(memory.cells.concrete().len(), 0);
        assert_eq!(memory.cells.runs().count(), 1);
        for index in [0, 1, count - 1] {
            assert_eq!(
                typed_load(&memory, &target.offset_by_bytes(index * 4)),
                typed_load(&before, &source.offset_by_bytes(index * 4))
            );
        }
        let saved = typed_load(&memory, &target);
        let changed = memory.store(source.clone(), CValue::UInt32(99u32.into()));
        assert_eq!(typed_load(&changed, &target), saved);
        samples.push((count, work));
    }
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 128),
        "{samples:?}"
    );
}

#[test]
fn external_array_execution_requires_full_authority_and_mutability() {
    let source = external(933_000);
    let target = external(933_001);
    let mut samples = Vec::new();
    for count in [1, 2, 4, 1024, 1_000_000] {
        for copy in [false, true] {
            for (read, write, mutable) in [
                (count, count, true),
                (count - 1, count, true),
                (count, count - 1, true),
                (count, count, false),
            ] {
                let state = CState::new().with_resource_context(
                    ResourceContext::new().unchecked_with_facts([
                        view_memory_fact(source.clone(), 0, read),
                        own_memory_fact(target.clone(), 0, write),
                    ]),
                );
                let target_value = CPointerValue::new(target.clone(), CType::UInt32Pointer)
                    .with_pointee_constant(!mutable);
                let (theorem, work) = crate::instrumentation::measure_deterministic_work(|| {
                    prove_c_statement_execution(
                        state,
                        c_write_scalar_array_region(
                            CExpression::Value(CValue::Pointer(target_value)),
                            if copy {
                                c_pointer_value(source.clone())
                            } else {
                                c_uint32_literal(7)
                            },
                            CType::UInt32,
                            count,
                            copy,
                        ),
                    )
                    .unwrap()
                });
                let valid = (!copy || read == count) && write == count && mutable;
                assert_eq!(
                    matches!(
                        theorem.proposition(),
                        Proposition::CStatementExecutes {
                            outcome: CStatementOutcome::Normal(_),
                            ..
                        }
                    ),
                    valid,
                    "count={count}, copy={copy}, read={read}, write={write}, mutable={mutable}",
                );
                if valid && copy {
                    samples.push(work);
                }
            }
        }
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 2 + 128),
        "bulk authority checks must stay compact: {samples:?}"
    );
}

#[test]
fn external_array_source_selection_skips_unrelated_parameter_cells() {
    let mut samples = Vec::new();
    for siblings in [1, 64, 2048] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = external(935_000);
        let target = Pointer {
            block: "local:indexed-copy".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut memory = CMemory::new()
            .with_block(target.block.clone(), 16)
            .store(source.clone(), CValue::UInt32(9u32.into()));
        for index in 0..siblings {
            memory = memory.store(external(936_000 + index), CValue::UInt32(11u32.into()));
        }
        let (copied, work) = crate::instrumentation::measure_deterministic_work(|| {
            copy(memory, &target, &source, 4)
        });
        assert_eq!(typed_load(&copied, &target), CValue::UInt32(9u32.into()));
        samples.push((siblings, work));
    }
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 256),
        "{samples:?}"
    );
}

#[test]
fn external_array_ambiguous_run_aliasing_forgets_without_extent_work() {
    let mut samples = Vec::new();
    for count in [8, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = external(939_000);
        let target = external(939_001);
        let other = external(939_002);
        let memory = copy(CMemory::new(), &target, &source, count);
        let before = memory.clone();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory.write_scalar_array_region(
                &other,
                CType::UInt32,
                count,
                CValue::pointer(target.clone()),
                true,
                false,
                &PureFactContext::new(),
            )
        });
        let copied = result.expect("ambiguous cache contents can be forgotten compactly");
        assert!(!copied.has_known_cell_at(&target));
        assert_eq!(copied.cells.runs().count(), 1);
        for index in [0, count - 1] {
            assert_eq!(
                typed_load(&copied, &other.offset_by_bytes(index * 4)),
                typed_load(&before, &target.offset_by_bytes(index * 4))
            );
        }
        samples.push((count, work));
    }
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 128),
        "{samples:?}"
    );
}
