use super::*;

// --- the canonicalization model's production invariants -------------------
// See docs/internals/canonicalization.md and issues/canonicalization.md.
// Production evaluation must never place a raw `MemoryLoad` inside
// pointer-offset arithmetic: loaded pointers and indices take their
// load variable first, and every load variable travels with its exact
// defining fact in the emitted facts. These tests drive the real
// evaluation entry points; kernel tests that construct raw load-bearing
// offsets directly do not establish this invariant.

/// Walks every pointer offset reachable from a value, collecting the
/// canonical load variables found in scaled positions and rejecting any
/// reachable raw `MemoryLoad` inside an `Int32Scaled` value.
fn collect_offset_names_from_value(value: &CValue, names: &mut BTreeSet<Variable>) {
    match value {
        CValue::Void => {}
        CValue::Int32(term) | CValue::UInt8(term) => {
            collect_offset_names_from_term(term, names);
        }
        CValue::Pointer(pointer) => {
            collect_offset_names_from_offset(&pointer.offset, names);
        }
    }
}

/// Walks a term in value position: load atoms are legitimate here, but
/// their pointers' offsets must satisfy the no-raw-load invariant.
fn collect_offset_names_from_term(term: &Bitvector32Term, names: &mut BTreeSet<Variable>) {
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => {}
        Bitvector32Term::MemoryLoad(_, pointer) => {
            collect_offset_names_from_offset(&pointer.offset, names);
        }
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right)
        | Bitvector32Term::Divide(left, right)
        | Bitvector32Term::Remainder(left, right)
        | Bitvector32Term::ShiftLeft(left, right)
        | Bitvector32Term::ArithmeticShiftRight(left, right)
        | Bitvector32Term::BitwiseAnd(left, right)
        | Bitvector32Term::BitwiseOr(left, right)
        | Bitvector32Term::BitwiseXor(left, right) => {
            collect_offset_names_from_term(left, names);
            collect_offset_names_from_term(right, names);
        }
        Bitvector32Term::BitwiseNot(value) => collect_offset_names_from_term(value, names),
        Bitvector32Term::If {
            condition: _,
            then_term,
            else_term,
        } => {
            collect_offset_names_from_term(then_term, names);
            collect_offset_names_from_term(else_term, names);
        }
        Bitvector32Term::RangeFold { .. } | Bitvector32Term::PureFunctionApplication { .. } => {}
    }
}

fn collect_offset_names_from_offset(offset: &PointerOffsetTerm, names: &mut BTreeSet<Variable>) {
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
        PointerOffsetTerm::Add(left, right) => {
            collect_offset_names_from_offset(left, names);
            collect_offset_names_from_offset(right, names);
        }
        PointerOffsetTerm::Int32Scaled { value, .. } => {
            assert_scaled_index_free_of_raw_loads(value, names);
        }
    }
}

/// Inside an `Int32Scaled` value no load term may appear; load variables
/// are recorded for the defining-fact check.
fn assert_scaled_index_free_of_raw_loads(term: &Bitvector32Term, names: &mut BTreeSet<Variable>) {
    match term {
        Bitvector32Term::Constant(_) => {}
        Bitvector32Term::Variable(variable) => {
            if crate::kernel::is_canonical_load_variable(variable) {
                names.insert(*variable);
            }
        }
        Bitvector32Term::MemoryLoad(_, _) => {
            panic!("production pointer offset contains a raw memory load: {term:?}")
        }
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right)
        | Bitvector32Term::Divide(left, right)
        | Bitvector32Term::Remainder(left, right)
        | Bitvector32Term::ShiftLeft(left, right)
        | Bitvector32Term::ArithmeticShiftRight(left, right)
        | Bitvector32Term::BitwiseAnd(left, right)
        | Bitvector32Term::BitwiseOr(left, right)
        | Bitvector32Term::BitwiseXor(left, right) => {
            assert_scaled_index_free_of_raw_loads(left, names);
            assert_scaled_index_free_of_raw_loads(right, names);
        }
        Bitvector32Term::BitwiseNot(value) => assert_scaled_index_free_of_raw_loads(value, names),
        Bitvector32Term::If {
            condition: _,
            then_term,
            else_term,
        } => {
            assert_scaled_index_free_of_raw_loads(then_term, names);
            assert_scaled_index_free_of_raw_loads(else_term, names);
        }
        Bitvector32Term::RangeFold { .. } | Bitvector32Term::PureFunctionApplication { .. } => {}
    }
}

/// Every load variable selected into an offset must carry its exact
/// defining fact in the path's emitted facts.
fn assert_names_have_defining_facts(names: &BTreeSet<Variable>, facts: &[ExecutionPureFact]) {
    for name in names {
        let defined = facts.iter().any(|fact| {
            crate::kernel::is_canonical_load_defining_fact(&fact.proposition)
                && matches!(
                    &fact.proposition,
                    Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, _), true)
                        if matches!(left.as_ref(), Bitvector32Term::Variable(variable) if variable == name)
                )
        });
        assert!(
            defined,
            "load variable {name:?} has no defining fact in the emitted facts"
        );
    }
}

// The loaded-array-index analogue of the test below (a raw `p + *len_ptr`
// index taking its load variable at the pointer-addition birth site) is
// still an open gap: introducing load variables at one offset-birth site
// while the lang-side segment and endpoint evaluators still emit load terms
// splits one load identity into two terms and breaks frame matching. See
// issues/canonicalization.md — production adoption must land atomically
// across every producer.

#[test]
fn pointer_loaded_from_an_opaque_cell_takes_a_canonical_offset() {
    let cell = Pointer {
        block: "pp".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("pp", 4);
    let state = CState::new()
        .with_local("pp", CValue::Pointer(cell.clone()))
        .with_memory(memory)
        .with_resource_context(read_context(cell, 0, 1));
    let statement = c_return(c_typed_load(c_variable("pp"), CType::Int32Pointer));
    let execution = prove_symbolic_c_execution_paths(state, statement, PureFactContext::new());

    assert!(!execution.paths().is_empty());
    let mut saw_a_canonical_offset = false;
    for path in execution.paths() {
        let Proposition::CStatementExecutes { outcome, .. } = path.theorem().proposition() else {
            panic!("execution should prove a statement judgment");
        };
        let CStatementOutcome::Return { value, .. } = outcome else {
            continue;
        };
        let mut names = BTreeSet::new();
        collect_offset_names_from_value(value, &mut names);
        assert_names_have_defining_facts(&names, &path.execution_facts());
        saw_a_canonical_offset |= !names.is_empty();
    }
    assert!(
        saw_a_canonical_offset,
        "the loaded pointer's offset should carry a load variable"
    );
}

// --- canonical form: determinism and idempotence --------------------------

#[test]
fn canonical_term_resolves_equal_loads_to_one_form() {
    let pointer = Pointer {
        block: "cells".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let base = CMemory::new().with_block("cells", 4);
    // The same unresolved load, read from two snapshots that differ only by
    // a block this load cannot observe.
    let drifted = base.clone().with_block("unrelated", 4);
    let load_at_base = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(base.clone()),
        Box::new(pointer.clone()),
    );
    let load_at_drifted = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(drifted),
        Box::new(pointer.clone()),
    );

    let canonical = crate::kernel::eval::canonical_term(&load_at_base);
    assert_eq!(
        canonical,
        crate::kernel::eval::canonical_term(&load_at_drifted),
        "representational snapshot drift must not change the canonical form"
    );
    let Bitvector32Term::Variable(name) = &canonical else {
        panic!("an unresolved load's canonical form is its load variable: {canonical:?}");
    };
    assert!(crate::kernel::is_canonical_load_variable(name));
    // Idempotence: the canonical form is its own canonical form.
    assert_eq!(canonical, crate::kernel::eval::canonical_term(&canonical));

    // A load whose cell is materialized resolves to the stored value.
    let stored = base.store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(7)));
    let resolved =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(stored), Box::new(pointer));
    assert_eq!(
        crate::kernel::eval::canonical_term(&resolved),
        Bitvector32Term::Constant(7)
    );
}

#[test]
fn offsets_match_modulo_canonical_names_through_the_canonical_form() {
    let pointer = Pointer {
        block: "cells".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let base = CMemory::new().with_block("cells", 4);
    let drifted = base.clone().with_block("unrelated", 4);
    let scaled = |memory: CMemory| PointerOffsetTerm::Int32Scaled {
        value: Box::new(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(memory),
            Box::new(pointer.clone()),
        )),
        byte_width: 4,
    };

    assert!(crate::kernel::offsets_match_modulo_canonical_names(
        &scaled(base.clone()),
        &scaled(drifted.clone()),
    ));
    // The load term and its load variable are one offset.
    let named = crate::kernel::eval::canonical_offset_term(&scaled(base.clone()));
    assert!(crate::kernel::offsets_match_modulo_canonical_names(
        &named,
        &scaled(drifted),
    ));
    // Distinct cells stay distinct.
    let other = Pointer {
        block: "cells".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let other_scaled = PointerOffsetTerm::Int32Scaled {
        value: Box::new(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(base.clone()),
            Box::new(other),
        )),
        byte_width: 4,
    };
    assert!(!crate::kernel::offsets_match_modulo_canonical_names(
        &scaled(base),
        &other_scaled,
    ));
}
