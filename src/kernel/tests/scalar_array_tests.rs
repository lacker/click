//! Compact scalar arrays keep checked authority independent of logical length.
use super::*;

fn pointer(block: &str, offset: i64) -> Pointer {
    Pointer {
        block: block.into(),
        offset: PointerOffsetTerm::Constant(offset),
    }
}
fn fresh(count: u32) -> CMemory {
    CMemory::new()
        .with_block("local:array-source", count * 4)
        .with_block("local:array-target", count * 4)
}
fn seeded(count: u32) -> CMemory {
    fresh(count)
        .initialize_scalar_array(
            &pointer("local:array-source", 0),
            CType::UInt32,
            count,
            CValue::UInt32(Bitvector32Term::Variable(Variable(912_345))),
            false,
        )
        .unwrap()
}

#[test]
fn compact_scalar_arrays_copy_uniform_values_without_expanding_storage_or_work() {
    let mut samples = Vec::new();
    for count in [8, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let (memory, work) = crate::instrumentation::measure_deterministic_work(|| {
            seeded(count)
                .initialize_scalar_array(
                    &pointer("local:array-target", 0),
                    CType::UInt32,
                    count,
                    CValue::pointer(pointer("local:array-source", 0)),
                    true,
                )
                .unwrap()
        });
        assert_eq!(memory.cells.concrete().len(), 0);
        assert_eq!(
            memory
                .cells
                .runs_in_block(&"local:array-source".into())
                .count(),
            1
        );
        assert_eq!(
            memory
                .cells
                .runs_in_block(&"local:array-target".into())
                .count(),
            1
        );
        assert_eq!(
            memory.load(&pointer("local:array-target", i64::from(count - 1) * 4)),
            CExpressionOutcome::Value(CValue::UInt32(Bitvector32Term::Variable(Variable(912_345))))
        );
        assert!(memory.has_initialized_bytes_at(&pointer("local:array-target", 0), count * 4));
        let mutated = memory.clone().store(
            pointer("local:array-source", 0),
            CValue::UInt32(99u32.into()),
        );
        assert_eq!(
            mutated.load(&pointer("local:array-target", 0)),
            memory.load(&pointer("local:array-target", 0))
        );
        samples.push((count, work));
    }
    eprintln!("uniform array initialization/copy (length, work): {samples:?}");
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 32),
        "{samples:?}"
    );
}

#[test]
fn compact_scalar_arrays_reject_nonuniform_uninitialized_and_partial_storage() {
    let source = pointer("local:array-source", 0);
    let target = pointer("local:array-target", 0);
    for memory in [
        fresh(4),
        seeded(4).store(source.clone(), CValue::UInt32(9u32.into())),
    ] {
        assert!(
            memory
                .initialize_scalar_array(
                    &target,
                    CType::UInt32,
                    4,
                    CValue::pointer(source.clone()),
                    true
                )
                .is_err()
        );
    }
    assert!(
        seeded(4)
            .initialize_scalar_array(
                &target,
                CType::UInt32,
                3,
                CValue::pointer(source.clone()),
                true
            )
            .is_err()
    );
    assert!(
        seeded(4)
            .initialize_scalar_array(
                &target,
                CType::Int32,
                4,
                CValue::pointer(source.clone()),
                true
            )
            .is_err()
    );
    let initialized = seeded(4)
        .initialize_scalar_array(&target, CType::UInt32, 4, CValue::pointer(source), true)
        .unwrap();
    assert!(
        initialized
            .initialize_scalar_array(
                &target,
                CType::UInt32,
                4,
                CValue::UInt32(9u32.into()),
                false
            )
            .is_err()
    );
    assert!(
        fresh(4)
            .initialize_scalar_array(
                &pointer("local:array-target", 4),
                CType::UInt32,
                3,
                CValue::UInt32(9u32.into()),
                false
            )
            .is_err()
    );
}

#[test]
fn compact_scalar_array_operations_require_complete_read_and_write_authority() {
    let source = pointer("local:array-source", 0);
    let target = pointer("local:array-target", 0);
    for copy in [false, true] {
        for complete in [false, true] {
            let mut resources = vec![own_memory_fact(
                target.clone(),
                0,
                if complete { 4 } else { 3 },
            )];
            if copy {
                resources.push(view_memory_fact(source.clone(), 0, 4));
            }
            let state = CState::new()
                .with_memory(if copy { seeded(4) } else { fresh(4) })
                .with_resource_context(ResourceContext::new().unchecked_with_facts(resources));
            let statement = c_initialize_scalar_array(
                c_pointer_value(target.clone()),
                if copy {
                    c_pointer_value(source.clone())
                } else {
                    c_uint32_literal(7)
                },
                CType::UInt32,
                4,
                copy,
            );
            let theorem = prove_c_statement_execution(state, statement).unwrap();
            let Proposition::CStatementExecutes { outcome, .. } = theorem.proposition() else {
                panic!()
            };
            if complete {
                assert!(
                    matches!(outcome, CStatementOutcome::Normal(_)),
                    "{outcome:?}"
                );
            } else {
                assert!(
                    matches!(
                        outcome,
                        CStatementOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
                    ),
                    "{outcome:?}"
                );
            }
        }
    }
    let state = CState::new().with_memory(seeded(4)).with_resource_context(
        ResourceContext::new().unchecked_with_facts(vec![
            own_memory_fact(target.clone(), 0, 4),
            view_memory_fact(source.clone(), 0, 3),
        ]),
    );
    let theorem = prove_c_statement_execution(
        state,
        c_initialize_scalar_array(
            c_pointer_value(target),
            c_pointer_value(source),
            CType::UInt32,
            4,
            true,
        ),
    )
    .unwrap();
    assert!(matches!(
        theorem.proposition(),
        Proposition::CStatementExecutes {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::MissingResource { .. }),
            ..
        }
    ));
}

#[test]
fn compact_scalar_array_zero_length_needs_no_byte_authority() {
    let state = CState::new().with_memory(fresh(0));
    let statement = c_seq(
        c_initialize_scalar_array(
            c_pointer_value(pointer("local:array-source", 0)),
            c_uint32_literal(7),
            CType::UInt32,
            0,
            false,
        ),
        c_initialize_scalar_array(
            c_pointer_value(pointer("local:array-target", 0)),
            c_pointer_value(pointer("local:array-source", 0)),
            CType::UInt32,
            0,
            true,
        ),
    );
    let theorem = prove_c_statement_execution(state, statement).unwrap();
    assert!(matches!(
        theorem.proposition(),
        Proposition::CStatementExecutes {
            outcome: CStatementOutcome::Normal(_),
            ..
        }
    ));
}

#[test]
fn compact_scalar_array_initialization_rejects_readonly_storage_and_pointer_qualifiers() {
    let target = pointer("local:array-target", 0);
    for readonly_block in [false, true] {
        let memory =
            CMemory::new().with_block_or_read_only(target.block.clone(), 16, readonly_block);
        let state = CState::new()
            .with_memory(memory)
            .with_resource_context(own_memory_context(target.clone(), 0, 4));
        let pointer = CPointerValue::new(target.clone(), CType::UInt32Pointer)
            .with_pointee_constant(!readonly_block);
        let theorem = prove_c_statement_execution(
            state,
            c_initialize_scalar_array(
                CExpression::Value(CValue::Pointer(pointer)),
                c_uint32_literal(7),
                CType::UInt32,
                4,
                false,
            ),
        )
        .unwrap();
        assert!(matches!(
            theorem.proposition(),
            Proposition::CStatementExecutes {
                outcome: CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
                ..
            }
        ));
    }
    let theorem = prove_c_statement_execution(
        CState::new().with_memory(fresh(0)),
        c_initialize_scalar_array(
            c_pointer_value(target),
            c_void_value(),
            CType::Void,
            0,
            false,
        ),
    )
    .unwrap();
    assert!(matches!(
        theorem.proposition(),
        Proposition::CStatementExecutes {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            ..
        }
    ));
}

#[test]
fn compact_scalar_array_initialization_cannot_bypass_an_active_view_loan() {
    let target = pointer("local:array-target", 0);
    let viewed = view_memory_fact(target.clone(), 0, 4);
    let resources = ResourceContext::new()
        .unchecked_with_facts([own_memory_fact(target.clone(), 0, 4), viewed.clone()]);
    let support = resources.occurrences_for_fact(&viewed)[0];
    let ledger = crate::kernel::loans::LoanLedger::new();
    let participant = ledger.fresh_participant().unwrap();
    let opening = ledger
        .borrowed_contract_input(participant, support, viewed.clone(), None)
        .unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let bindings = crate::kernel::loans::LoanViewBindings::default().with_inserted(
        support,
        crate::kernel::loans::LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed,
            hold: None,
        },
    );
    let state = CState::new()
        .with_memory(fresh(4))
        .with_resource_context(resources)
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(participant))
        .with_loan_view_bindings(bindings);
    let theorem = prove_c_statement_execution(
        state,
        c_initialize_scalar_array(
            c_pointer_value(target),
            c_uint32_literal(7),
            CType::UInt32,
            4,
            false,
        ),
    )
    .unwrap();
    assert!(matches!(
        theorem.proposition(),
        Proposition::CStatementExecutes {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_)),
            ..
        }
    ));
}
