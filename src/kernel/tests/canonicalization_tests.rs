use super::*;

// --- the canonicalization model's production invariants -------------------
// See docs/internals/canonicalization.md.
// Production evaluation must never place a raw `MemoryLoad` inside
// pointer-offset arithmetic: loaded pointers and indices take their
// load variable first, and every load variable travels with its exact
// defining fact in the emitted facts. These tests drive the real
// evaluation entry points; kernel tests that construct raw load-bearing
// offsets directly do not establish this invariant.

/// Walks every pointer offset reachable from a value, collecting the
/// load variables found in scaled positions and rejecting any
/// reachable raw `MemoryLoad` inside an `Int32Scaled` value.
fn collect_offset_load_variables_from_value(
    value: &CValue,
    load_variables: &mut BTreeSet<Variable>,
) {
    match value {
        CValue::Void => {}
        CValue::Int32(term) | CValue::UInt8(term) => {
            collect_offset_load_variables_from_term(term, load_variables);
        }
        CValue::Pointer(pointer) => {
            collect_offset_load_variables_from_offset(&pointer.offset, load_variables);
        }
    }
}

/// Walks a term in value position: load atoms are legitimate here, but
/// their pointers' offsets must satisfy the no-raw-load invariant.
fn collect_offset_load_variables_from_term(
    term: &Bitvector32Term,
    load_variables: &mut BTreeSet<Variable>,
) {
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => {}
        Bitvector32Term::MemoryLoad(_, pointer) => {
            collect_offset_load_variables_from_offset(&pointer.offset, load_variables);
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
            collect_offset_load_variables_from_term(left, load_variables);
            collect_offset_load_variables_from_term(right, load_variables);
        }
        Bitvector32Term::BitwiseNot(value) => {
            collect_offset_load_variables_from_term(value, load_variables)
        }
        Bitvector32Term::If {
            condition: _,
            then_term,
            else_term,
        } => {
            collect_offset_load_variables_from_term(then_term, load_variables);
            collect_offset_load_variables_from_term(else_term, load_variables);
        }
        Bitvector32Term::RangeFold { .. } | Bitvector32Term::PureFunctionApplication { .. } => {}
    }
}

fn collect_offset_load_variables_from_offset(
    offset: &PointerOffsetTerm,
    load_variables: &mut BTreeSet<Variable>,
) {
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
        PointerOffsetTerm::Add(left, right) => {
            collect_offset_load_variables_from_offset(left, load_variables);
            collect_offset_load_variables_from_offset(right, load_variables);
        }
        PointerOffsetTerm::Int32Scaled { value, .. } => {
            assert_scaled_index_free_of_raw_loads(value, load_variables);
        }
    }
}

/// Inside an `Int32Scaled` value no load term may appear; load variables
/// are recorded for the defining-fact check.
fn assert_scaled_index_free_of_raw_loads(
    term: &Bitvector32Term,
    load_variables: &mut BTreeSet<Variable>,
) {
    match term {
        Bitvector32Term::Constant(_) => {}
        Bitvector32Term::Variable(variable) => {
            if crate::kernel::is_load_variable(variable) {
                load_variables.insert(*variable);
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
            assert_scaled_index_free_of_raw_loads(left, load_variables);
            assert_scaled_index_free_of_raw_loads(right, load_variables);
        }
        Bitvector32Term::BitwiseNot(value) => {
            assert_scaled_index_free_of_raw_loads(value, load_variables)
        }
        Bitvector32Term::If {
            condition: _,
            then_term,
            else_term,
        } => {
            assert_scaled_index_free_of_raw_loads(then_term, load_variables);
            assert_scaled_index_free_of_raw_loads(else_term, load_variables);
        }
        Bitvector32Term::RangeFold { .. } | Bitvector32Term::PureFunctionApplication { .. } => {}
    }
}

/// Every load variable selected into an offset must carry its exact
/// defining fact in the path's emitted facts.
fn assert_load_variables_have_defining_facts(
    load_variables: &BTreeSet<Variable>,
    facts: &[ExecutionPureFact],
) {
    for load_variable in load_variables {
        let defined = facts.iter().any(|fact| {
            crate::kernel::is_load_variable_defining_fact(&fact.proposition)
                && matches!(
                    &fact.proposition,
                    Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, _), true)
                        if matches!(left.as_ref(), Bitvector32Term::Variable(variable) if variable == load_variable)
                )
        });
        assert!(
            defined,
            "load variable {load_variable:?} has no defining fact in the emitted facts"
        );
    }
}

/// The loaded-array-index half of the representation invariant: the index
/// `*len_ptr` of `data + *len_ptr` is a load variable in the resulting
/// offset (never a raw load), and the registry associates the load variable
/// with its opaque cell. The defining equation is a tautology of the canonical
/// model, so the operand merge drops it from the path facts; the registry, not
/// the fact stream, is what ties a load variable to its cell.
#[test]
fn index_loaded_from_an_opaque_cell_takes_a_canonical_offset() {
    let len_cell = Pointer {
        block: "len".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let data = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("len", 4).with_block("data", 64);
    let state = CState::new()
        .with_local("len_ptr", CValue::Pointer(len_cell.clone()))
        .with_local("data", CValue::Pointer(data))
        .with_memory(memory)
        .with_resource_context(view_memory_context(len_cell.clone(), 0, 1));
    let statement = c_return(c_add(
        c_variable("data"),
        c_typed_load(c_variable("len_ptr"), CType::Int32),
    ));
    let execution = prove_symbolic_c_execution_paths(state, statement, PureFactContext::new());

    assert!(!execution.paths().is_empty());
    let mut saw_a_canonical_offset = false;
    for path in execution.paths() {
        let Proposition::CStatementExecutes { outcome, .. } =
            path.theorem().proposition().peel_implications()
        else {
            panic!("execution should prove a statement judgment");
        };
        let CStatementOutcome::Return { value, .. } = outcome else {
            continue;
        };
        let mut load_variables = BTreeSet::new();
        collect_offset_load_variables_from_value(value, &mut load_variables);
        for load_variable in &load_variables {
            let (_, pointer) = crate::kernel::registered_load_for_variable(load_variable)
                .expect("the index's load variable should be registered");
            assert_eq!(
                pointer, len_cell,
                "the load variable should denote the loaded index cell"
            );
        }
        saw_a_canonical_offset |= !load_variables.is_empty();
    }
    assert!(
        saw_a_canonical_offset,
        "the loaded index's offset should carry a load variable"
    );
}

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
        .with_resource_context(view_memory_context(cell, 0, 1));
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
        let mut load_variables = BTreeSet::new();
        collect_offset_load_variables_from_value(value, &mut load_variables);
        assert_load_variables_have_defining_facts(&load_variables, &path.execution_facts());
        saw_a_canonical_offset |= !load_variables.is_empty();
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
    let Bitvector32Term::Variable(load_variable) = &canonical else {
        panic!("an unresolved load's canonical form is its load variable: {canonical:?}");
    };
    assert!(crate::kernel::is_load_variable(load_variable));
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
fn offsets_have_same_canonical_form_through_the_canonical_form() {
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

    assert!(crate::kernel::offsets_have_same_canonical_form(
        &scaled(base.clone()),
        &scaled(drifted.clone()),
    ));
    // The load term and its load variable are one offset.
    let named = crate::kernel::eval::canonical_offset_term(&scaled(base.clone()));
    assert!(crate::kernel::offsets_have_same_canonical_form(
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
    assert!(!crate::kernel::offsets_have_same_canonical_form(
        &scaled(base),
        &other_scaled,
    ));
}

#[test]
fn load_variables_are_congruent_through_ground_index_equalities() {
    // `data[index]` with `index == 0` in scope is the cell `data[0]`: the
    // two load variables are content-addressed by different addresses, so
    // comparison joins them by congruence rather than by a shared load variable.
    let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("data", 8));
    let index = Bitvector32Term::Variable(Variable(7));
    let indexed = Bitvector32Term::MemoryLoad(
        memory.clone(),
        Box::new(Pointer {
            block: "data".into(),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(index.clone()),
                byte_width: 4,
            },
        }),
    );
    let first = Bitvector32Term::MemoryLoad(
        memory,
        Box::new(Pointer {
            block: "data".into(),
            offset: PointerOffsetTerm::Constant(0),
        }),
    );
    let indexed_load_variable = crate::kernel::eval::canonical_term(&indexed);
    let first_load_variable = crate::kernel::eval::canonical_term(&first);
    assert_ne!(
        indexed_load_variable, first_load_variable,
        "distinct addresses take distinct load variables"
    );

    let without_index_fact = PureFactContext::new();
    assert!(
        !without_index_fact
            .bitvector_terms_equal_from_facts(&indexed_load_variable, &first_load_variable)
    );

    let with_index_fact = PureFactContext::new().assume_condition(
        ConditionTerm::equal(index, Bitvector32Term::Constant(0)),
        true,
    );
    assert!(
        with_index_fact
            .bitvector_terms_equal_from_facts(&indexed_load_variable, &first_load_variable)
    );
    assert!(
        with_index_fact
            .bitvector_terms_equal_from_facts(&first_load_variable, &indexed_load_variable)
    );
    // A different constant index selects a different cell.
    let other = PureFactContext::new().assume_condition(
        ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(7)),
            Bitvector32Term::Constant(1),
        ),
        true,
    );
    assert!(!other.bitvector_terms_equal_from_facts(&indexed_load_variable, &first_load_variable));
}

#[test]
fn substitution_reaches_through_a_load_variable_with_a_bound_index() {
    // A universal's body contains `p[k]` with the bound `k` inside
    // the load variable's address. Instantiating `k := 0` must reach through
    // the load variable and produce the load variable used by a direct read
    // of `p[0]`.
    let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("p", 12));
    let bound = Variable(3_000_000);
    let cell = |offset: PointerOffsetTerm| {
        Bitvector32Term::MemoryLoad(
            memory.clone(),
            Box::new(Pointer {
                block: "p".into(),
                offset,
            }),
        )
    };
    let indexed_load_variable =
        crate::kernel::eval::canonical_term(&cell(PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(bound)),
            byte_width: 4,
        }));
    assert!(matches!(
        indexed_load_variable,
        Bitvector32Term::Variable(_)
    ));
    let instantiated = crate::kernel::reasoning::substitute_bitvector_variable(
        &indexed_load_variable,
        bound,
        &Bitvector32Term::Constant(0),
    );
    assert_eq!(
        instantiated,
        crate::kernel::eval::canonical_term(&cell(PointerOffsetTerm::Constant(0)))
    );
    // Substituting an unrelated variable leaves the load variable untouched.
    assert_eq!(
        crate::kernel::reasoning::substitute_bitvector_variable(
            &indexed_load_variable,
            Variable(3_000_001),
            &Bitvector32Term::Constant(0),
        ),
        indexed_load_variable
    );
}

#[test]
fn load_variables_compare_as_loads_under_bounds_pinned_indices() {
    // `p[j]` and `p[2]` are one cell when `j <= 2` and `not (j < 2)`: no
    // recorded equality mentions the index, so the comparison must view the
    // load variables as their loads and decide the addresses from bounds.
    let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("p", 12));
    let j = Bitvector32Term::Variable(Variable(7));
    let cell = |offset: PointerOffsetTerm| {
        crate::kernel::eval::canonical_term(&Bitvector32Term::MemoryLoad(
            memory.clone(),
            Box::new(Pointer {
                block: "p".into(),
                offset,
            }),
        ))
    };
    let indexed = cell(PointerOffsetTerm::Int32Scaled {
        value: Box::new(j.clone()),
        byte_width: 4,
    });
    let third = cell(PointerOffsetTerm::Constant(8));
    assert_ne!(indexed, third);
    // The index is a free variable of the load variable's denotation.
    let mut variables = BTreeSet::new();
    crate::kernel::reasoning::collect_bitvector_variables(&indexed, &mut variables);
    assert!(variables.contains(&Variable(7)));

    let pinned = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(j.clone(), Bitvector32Term::Constant(2)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j.clone(), Bitvector32Term::Constant(2)),
            false,
        );
    assert!(pinned.bitvector_terms_proven_equal(&indexed, &third));
    assert!(!PureFactContext::new().bitvector_terms_proven_equal(&indexed, &third));
}

#[test]
fn load_variable_free_variables_include_its_snapshot_cells() {
    // A load variable over a snapshot whose cells mention a loop counter
    // denotes a term mentioning that counter: finite context splits keyed on
    // a goal's variables must see it through the load variable.
    let counter = Variable(11);
    let written = CMemory::new().with_block("p", 12).store(
        Pointer {
            block: "p".into(),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(counter)),
                byte_width: 4,
            },
        },
        CValue::Int32(Bitvector32Term::Constant(5)),
    );
    let load_variable = crate::kernel::eval::canonical_term(&Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(written),
        Box::new(Pointer {
            block: "p".into(),
            offset: PointerOffsetTerm::Constant(8),
        }),
    ));
    assert!(matches!(load_variable, Bitvector32Term::Variable(_)));
    let mut variables = BTreeSet::new();
    crate::kernel::reasoning::collect_bitvector_variables(&load_variable, &mut variables);
    assert!(variables.contains(&counter));
}
