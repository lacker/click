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
        CValue::Int16(term)
        | CValue::Int32(term)
        | CValue::UInt8(term)
        | CValue::UInt16(term)
        | CValue::UInt32(term)
        | CValue::Int64(term)
        | CValue::UInt64(term)
        | CValue::Float32(term)
        | CValue::Float64(term) => {
            collect_offset_load_variables_from_term(term, load_variables);
        }
        CValue::Pointer(pointer) => {
            collect_offset_load_variables_from_offset(&pointer.offset, load_variables);
        }
    }
}

#[test]
fn floating_values_keep_their_declared_width_and_opaque_payload() {
    let float_pointer = Pointer {
        block: "float-storage".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let float_value = CValue::Float32(Bitvector32Term::Constant(0x8000_0000));
    let float_memory = CMemory::new()
        .with_block("float-storage", 4)
        .store(float_pointer.clone(), float_value.clone());
    assert_eq!(float_value.c_type(), CType::Float32);
    assert_eq!(float_value.byte_width(), 4);
    assert!(CType::Float32.accepts(&float_value));
    assert_eq!(
        float_memory.load(&float_pointer),
        CExpressionOutcome::Value(float_value.clone())
    );
    assert_eq!(
        float_memory.symbolic_float32_load(&float_pointer).c_type(),
        CType::Float32
    );

    let double_pointer = Pointer {
        block: "double-storage".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let double_value = CValue::Float64(Bitvector32Term::UInt64Constant(0x7ff8_0000_0000_0001));
    let double_memory = CMemory::new()
        .with_block("double-storage", 8)
        .store(double_pointer.clone(), double_value.clone());
    assert_eq!(double_value.c_type(), CType::Float64);
    assert_eq!(double_value.byte_width(), 8);
    assert!(CType::Float64.accepts(&double_value));
    assert_eq!(
        double_memory.load(&double_pointer),
        CExpressionOutcome::Value(double_value)
    );
    assert_eq!(
        double_memory
            .symbolic_float64_load(&double_pointer)
            .c_type(),
        CType::Float64
    );
}

/// Walks a term in value position: load atoms are legitimate here, but
/// their pointers' offsets must satisfy the no-raw-load invariant.
fn collect_offset_load_variables_from_term(
    term: &Bitvector32Term,
    load_variables: &mut BTreeSet<Variable>,
) {
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::Variable(_) => {}
        Bitvector32Term::MemoryLoad(_, pointer) | Bitvector32Term::PointerAddress(pointer) => {
            collect_offset_load_variables_from_offset(&pointer.offset, load_variables);
        }
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right)
        | Bitvector32Term::Divide(left, right)
        | Bitvector32Term::UnsignedDivide(left, right)
        | Bitvector32Term::Remainder(left, right)
        | Bitvector32Term::UnsignedRemainder(left, right)
        | Bitvector32Term::ShiftLeft(left, right)
        | Bitvector32Term::ArithmeticShiftRight(left, right)
        | Bitvector32Term::LogicalShiftRight(left, right)
        | Bitvector32Term::BitwiseAnd(left, right)
        | Bitvector32Term::BitwiseOr(left, right)
        | Bitvector32Term::BitwiseXor(left, right) => {
            collect_offset_load_variables_from_term(left, load_variables);
            collect_offset_load_variables_from_term(right, load_variables);
        }
        Bitvector32Term::Float32Binary { left, right, .. }
        | Bitvector32Term::Float64Binary { left, right, .. } => {
            collect_offset_load_variables_from_term(left, load_variables);
            collect_offset_load_variables_from_term(right, load_variables);
        }
        Bitvector32Term::Float32Negate(value) | Bitvector32Term::Float64Negate(value) => {
            collect_offset_load_variables_from_term(value, load_variables);
        }
        Bitvector32Term::Int64From32(value)
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value)
        | Bitvector32Term::Int64BitwiseNot(value)
        | Bitvector32Term::UInt64BitwiseNot(value) => {
            collect_offset_load_variables_from_term(value, load_variables);
        }
        Bitvector32Term::Int64Add(left, right)
        | Bitvector32Term::Int64Subtract(left, right)
        | Bitvector32Term::Int64Multiply(left, right)
        | Bitvector32Term::Int64Divide(left, right)
        | Bitvector32Term::Int64Remainder(left, right)
        | Bitvector32Term::Int64ShiftLeft(left, right)
        | Bitvector32Term::Int64ArithmeticShiftRight(left, right)
        | Bitvector32Term::Int64BitwiseAnd(left, right)
        | Bitvector32Term::Int64BitwiseOr(left, right)
        | Bitvector32Term::Int64BitwiseXor(left, right)
        | Bitvector32Term::UInt64Add(left, right)
        | Bitvector32Term::UInt64Subtract(left, right)
        | Bitvector32Term::UInt64Multiply(left, right)
        | Bitvector32Term::UInt64Divide(left, right)
        | Bitvector32Term::UInt64Remainder(left, right)
        | Bitvector32Term::UInt64ShiftLeft(left, right)
        | Bitvector32Term::UInt64LogicalShiftRight(left, right)
        | Bitvector32Term::UInt64BitwiseAnd(left, right)
        | Bitvector32Term::UInt64BitwiseOr(left, right)
        | Bitvector32Term::UInt64BitwiseXor(left, right) => {
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
        PointerOffsetTerm::Int32Scaled { value, .. }
        | PointerOffsetTerm::Int64Scaled { value, .. } => {
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
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_) => {}
        Bitvector32Term::Variable(variable) => {
            if crate::kernel::is_load_variable(variable) {
                load_variables.insert(*variable);
            }
        }
        Bitvector32Term::MemoryLoad(_, _) => {
            panic!("production pointer offset contains a raw memory load: {term:?}")
        }
        Bitvector32Term::PointerAddress(pointer) => {
            for value in pointer.offset.scaled_values() {
                assert_scaled_index_free_of_raw_loads(value, load_variables);
            }
        }
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right)
        | Bitvector32Term::Divide(left, right)
        | Bitvector32Term::UnsignedDivide(left, right)
        | Bitvector32Term::Remainder(left, right)
        | Bitvector32Term::UnsignedRemainder(left, right)
        | Bitvector32Term::ShiftLeft(left, right)
        | Bitvector32Term::ArithmeticShiftRight(left, right)
        | Bitvector32Term::LogicalShiftRight(left, right)
        | Bitvector32Term::BitwiseAnd(left, right)
        | Bitvector32Term::BitwiseOr(left, right)
        | Bitvector32Term::BitwiseXor(left, right) => {
            assert_scaled_index_free_of_raw_loads(left, load_variables);
            assert_scaled_index_free_of_raw_loads(right, load_variables);
        }
        Bitvector32Term::Int64From32(value)
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value)
        | Bitvector32Term::Int64BitwiseNot(value)
        | Bitvector32Term::UInt64BitwiseNot(value) => {
            assert_scaled_index_free_of_raw_loads(value, load_variables);
        }
        Bitvector32Term::Int64Add(left, right)
        | Bitvector32Term::Int64Subtract(left, right)
        | Bitvector32Term::Int64Multiply(left, right)
        | Bitvector32Term::Int64Divide(left, right)
        | Bitvector32Term::Int64Remainder(left, right)
        | Bitvector32Term::Int64ShiftLeft(left, right)
        | Bitvector32Term::Int64ArithmeticShiftRight(left, right)
        | Bitvector32Term::Int64BitwiseAnd(left, right)
        | Bitvector32Term::Int64BitwiseOr(left, right)
        | Bitvector32Term::Int64BitwiseXor(left, right)
        | Bitvector32Term::UInt64Add(left, right)
        | Bitvector32Term::UInt64Subtract(left, right)
        | Bitvector32Term::UInt64Multiply(left, right)
        | Bitvector32Term::UInt64Divide(left, right)
        | Bitvector32Term::UInt64Remainder(left, right)
        | Bitvector32Term::UInt64ShiftLeft(left, right)
        | Bitvector32Term::UInt64LogicalShiftRight(left, right)
        | Bitvector32Term::UInt64BitwiseAnd(left, right)
        | Bitvector32Term::UInt64BitwiseOr(left, right)
        | Bitvector32Term::UInt64BitwiseXor(left, right) => {
            assert_scaled_index_free_of_raw_loads(left, load_variables);
            assert_scaled_index_free_of_raw_loads(right, load_variables);
        }
        Bitvector32Term::BitwiseNot(value) => {
            assert_scaled_index_free_of_raw_loads(value, load_variables)
        }
        Bitvector32Term::Float32Negate(value) | Bitvector32Term::Float64Negate(value) => {
            assert_scaled_index_free_of_raw_loads(value, load_variables)
        }
        Bitvector32Term::Float32Binary { left, right, .. }
        | Bitvector32Term::Float64Binary { left, right, .. } => {
            assert_scaled_index_free_of_raw_loads(left, load_variables);
            assert_scaled_index_free_of_raw_loads(right, load_variables);
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
        .with_local("len_ptr", CValue::pointer(len_cell.clone()))
        .with_local("data", CValue::pointer(data))
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
        .with_local("pp", CValue::pointer(cell.clone()))
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

fn unresolved_canonicalization_test_load() -> Bitvector32Term {
    let memory = CMemory::new().with_block("canonical-shapes", 8);
    Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory),
        Box::new(Pointer {
            block: "canonical-shapes".into(),
            offset: PointerOffsetTerm::Constant(0),
        }),
    )
}

#[test]
fn canonical_term_is_idempotent_for_every_term_shape() {
    macro_rules! binary {
        ($variant:ident, $left:expr, $right:expr) => {
            Bitvector32Term::$variant(Box::new($left), Box::new($right))
        };
    }
    macro_rules! unary {
        ($variant:ident, $value:expr) => {
            Bitvector32Term::$variant(Box::new($value))
        };
    }

    let load = unresolved_canonicalization_test_load();
    let u32_value = Bitvector32Term::Constant(3);
    let i64_value = Bitvector32Term::Int64Constant(3);
    let u64_value = Bitvector32Term::UInt64Constant(3);
    let terms = vec![
        Bitvector32Term::Constant(3),
        Bitvector32Term::Int64Constant(3),
        Bitvector32Term::UInt64Constant(3),
        Bitvector32Term::Variable(Variable(30_001)),
        binary!(Add, load.clone(), u32_value.clone()),
        binary!(Subtract, load.clone(), u32_value.clone()),
        binary!(Multiply, load.clone(), u32_value.clone()),
        binary!(Divide, load.clone(), u32_value.clone()),
        binary!(UnsignedDivide, load.clone(), u32_value.clone()),
        binary!(Remainder, load.clone(), u32_value.clone()),
        binary!(UnsignedRemainder, load.clone(), u32_value.clone()),
        binary!(ShiftLeft, load.clone(), u32_value.clone()),
        binary!(ArithmeticShiftRight, load.clone(), u32_value.clone()),
        binary!(LogicalShiftRight, load.clone(), u32_value.clone()),
        binary!(BitwiseAnd, load.clone(), u32_value.clone()),
        binary!(BitwiseOr, load.clone(), u32_value.clone()),
        binary!(BitwiseXor, load.clone(), u32_value.clone()),
        unary!(BitwiseNot, load.clone()),
        Bitvector32Term::If {
            condition: Box::new(ConditionTerm::Bitvector32Equal(
                Box::new(load.clone()),
                Box::new(u32_value.clone()),
            )),
            then_term: Box::new(load.clone()),
            else_term: Box::new(u32_value.clone()),
        },
        Bitvector32Term::RangeFold {
            start: Box::new(load.clone()),
            end: Box::new(u32_value.clone()),
            initial: Box::new(load.clone()),
            accumulator: Variable(30_002),
            item: Variable(30_003),
            body: Box::new(load.clone()),
        },
        Bitvector32Term::PureFunctionApplication {
            name: "canonical_shapes".to_string(),
            arguments: vec![load.clone(), u32_value.clone()],
        },
        load.clone(),
        unary!(Int64From32, load.clone()),
        unary!(UInt64From32, load.clone()),
        unary!(Int64FromUInt32, load.clone()),
        unary!(UInt64FromInt32, load.clone()),
        unary!(UInt64FromInt64, load.clone()),
        unary!(Int64BitwiseNot, load.clone()),
        unary!(UInt64BitwiseNot, load.clone()),
        binary!(Int64Add, load.clone(), i64_value.clone()),
        binary!(Int64Subtract, load.clone(), i64_value.clone()),
        binary!(Int64Multiply, load.clone(), i64_value.clone()),
        binary!(Int64Divide, load.clone(), i64_value.clone()),
        binary!(Int64Remainder, load.clone(), i64_value.clone()),
        binary!(Int64ShiftLeft, load.clone(), i64_value.clone()),
        binary!(Int64ArithmeticShiftRight, load.clone(), i64_value.clone()),
        binary!(Int64BitwiseAnd, load.clone(), i64_value.clone()),
        binary!(Int64BitwiseOr, load.clone(), i64_value.clone()),
        binary!(Int64BitwiseXor, load.clone(), i64_value.clone()),
        binary!(UInt64Add, load.clone(), u64_value.clone()),
        binary!(UInt64Subtract, load.clone(), u64_value.clone()),
        binary!(UInt64Multiply, load.clone(), u64_value.clone()),
        binary!(UInt64Divide, load.clone(), u64_value.clone()),
        binary!(UInt64Remainder, load.clone(), u64_value.clone()),
        binary!(UInt64ShiftLeft, load.clone(), u64_value.clone()),
        binary!(UInt64LogicalShiftRight, load.clone(), u64_value.clone()),
        binary!(UInt64BitwiseAnd, load.clone(), u64_value.clone()),
        binary!(UInt64BitwiseOr, load.clone(), u64_value.clone()),
        binary!(UInt64BitwiseXor, load, u64_value),
    ];

    for term in terms {
        let once = crate::kernel::eval::canonical_term(&term);
        assert_eq!(
            crate::kernel::eval::canonical_term(&once),
            once,
            "canonicalization was not idempotent for {term:?}",
        );
    }
}

#[test]
fn canonical_term_is_idempotent_at_multiple_term_depths() {
    let mut samples = Vec::new();
    for target_depth in [1_usize, 8, 32, 96, 256] {
        let mut term = unresolved_canonicalization_test_load();
        for depth in 0..target_depth {
            term = Bitvector32Term::Add(
                Box::new(Bitvector32Term::If {
                    condition: Box::new(ConditionTerm::Bitvector32Equal(
                        Box::new(term),
                        Box::new(Bitvector32Term::Constant(depth as u32)),
                    )),
                    then_term: Box::new(unresolved_canonicalization_test_load()),
                    else_term: Box::new(Bitvector32Term::Constant(depth as u32 + 1)),
                }),
                Box::new(Bitvector32Term::Constant(depth as u32 + 2)),
            );
        }

        crate::kernel::memory_provenance::reset_atomic_canonicalization_term_visits();
        crate::kernel::eval::reset_load_substitution_term_visits();
        let once = crate::kernel::eval::canonical_term(&term);
        let atomic_visits = crate::kernel::memory_provenance::atomic_canonicalization_term_visits();
        let substitution_visits = crate::kernel::eval::load_substitution_term_visits();
        assert!(atomic_visits <= 7 * target_depth + 2);
        assert!(substitution_visits <= 7 * target_depth + 2);
        samples.push((target_depth, atomic_visits, substitution_visits));
        assert_eq!(
            crate::kernel::eval::canonical_term(&once),
            once,
            "canonicalization was not idempotent at depth {target_depth}",
        );
    }
    assert!(samples[4].1 <= 260 * samples[0].1);
    assert!(samples[4].2 <= 260 * samples[0].2);
    eprintln!("canonical term depth work: {samples:?}");
}

#[test]
fn canonical_term_is_independent_of_contextual_equalities() {
    let term = Bitvector32Term::Variable(Variable(30_004));
    let canonical = crate::kernel::eval::canonical_term(&term);
    let equal_to_one = PureFactContext::new().assume_condition(
        ConditionTerm::Bitvector32Equal(
            Box::new(term.clone()),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        true,
    );
    let equal_to_two = PureFactContext::new().assume_condition(
        ConditionTerm::Bitvector32Equal(
            Box::new(term.clone()),
            Box::new(Bitvector32Term::Constant(2)),
        ),
        true,
    );

    let equals = |value| {
        Proposition::ConditionIs(
            ConditionTerm::equal(term.clone(), Bitvector32Term::Constant(value)),
            true,
        )
    };
    assert!(equal_to_one.derive_proposition(&equals(1)).is_some());
    assert!(equal_to_two.derive_proposition(&equals(2)).is_some());
    assert_eq!(crate::kernel::eval::canonical_term(&term), canonical);
    assert_eq!(canonical, term);
}

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
fn atomic_canonicalization_reaches_loads_in_every_condition_region() {
    let pointer = Pointer {
        block: "condition-cells".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new()
        .with_block("condition-cells", 4)
        .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(7)));
    let load =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(memory), Box::new(pointer));
    let overflow = Bitvector32Term::If {
        condition: Box::new(ConditionTerm::Bitvector32SignedAddOverflows(
            Box::new(load.clone()),
            Box::new(Bitvector32Term::Constant(1)),
        )),
        then_term: Box::new(Bitvector32Term::Constant(2)),
        else_term: Box::new(Bitvector32Term::Constant(3)),
    };
    let pointer_offset = Bitvector32Term::If {
        condition: Box::new(ConditionTerm::PointerOffsetEqual(
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(load),
                byte_width: 4,
            }),
            Box::new(PointerOffsetTerm::Constant(28)),
        )),
        then_term: Box::new(Bitvector32Term::Constant(4)),
        else_term: Box::new(Bitvector32Term::Constant(5)),
    };

    let canonical_overflow = crate::kernel::api::canonicalize_atomic_loads(&overflow);
    let Bitvector32Term::If { condition, .. } = canonical_overflow else {
        panic!("expected conditional term");
    };
    assert!(matches!(
        condition.as_ref(),
        ConditionTerm::Bitvector32SignedAddOverflows(left, _)
            if left.as_ref() == &Bitvector32Term::Constant(7)
    ));

    let canonical_pointer_offset = crate::kernel::api::canonicalize_atomic_loads(&pointer_offset);
    let Bitvector32Term::If { condition, .. } = canonical_pointer_offset else {
        panic!("expected conditional term");
    };
    assert!(matches!(
        condition.as_ref(),
        ConditionTerm::PointerOffsetEqual(left, _)
            if left.as_ref() == &PointerOffsetTerm::Constant(28)
    ));
}

#[test]
fn representational_load_equality_holds_beyond_the_former_depth_preflight() {
    let pointer = Pointer {
        block: "deep-cells".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let base = CMemory::new().with_block("deep-cells", 4);
    let drifted = base.clone().with_block("unrelated", 4);
    let mut left = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(base),
        Box::new(pointer.clone()),
    );
    let mut right =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(drifted), Box::new(pointer));
    for value in 0..128 {
        left = Bitvector32Term::Add(Box::new(left), Box::new(Bitvector32Term::Constant(value)));
        right = Bitvector32Term::Add(Box::new(right), Box::new(Bitvector32Term::Constant(value)));
    }

    assert_eq!(
        crate::kernel::eval::canonical_term(&left),
        crate::kernel::eval::canonical_term(&right),
    );
    assert!(PureFactContext::new().proves(&Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
        true,
    )));
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
fn canonical_offset_term_is_complete_and_idempotent_at_multiple_depths() {
    for depth in [64, 128, 256] {
        let mut offset = PointerOffsetTerm::Int32Scaled {
            value: Box::new(unresolved_canonicalization_test_load()),
            byte_width: 4,
        };
        for _ in 0..depth {
            offset =
                PointerOffsetTerm::Add(Box::new(offset), Box::new(PointerOffsetTerm::Constant(1)));
        }

        let canonical = crate::kernel::eval::canonical_offset_term(&offset);
        assert_eq!(
            crate::kernel::eval::canonical_offset_term(&canonical),
            canonical,
            "offset canonicalization was not idempotent at depth {depth}",
        );
        let mut leaf = &canonical;
        while let PointerOffsetTerm::Add(left, _) = leaf {
            leaf = left;
        }
        assert!(
            matches!(
                leaf,
                PointerOffsetTerm::Int32Scaled { value, .. }
                    if matches!(value.as_ref(), Bitvector32Term::Variable(variable) if crate::kernel::is_load_variable(variable))
            ),
            "the deepest scaled index should take its load variable at depth {depth}: {leaf:?}",
        );
    }
}

#[test]
fn pointer_offset_add_coalesces_nested_constant_displacements() {
    let base = PointerOffsetTerm::Int32Scaled {
        value: Box::new(Bitvector32Term::Variable(Variable(17))),
        byte_width: 4,
    };
    let nested = PointerOffsetTerm::add(
        PointerOffsetTerm::add(base.clone(), PointerOffsetTerm::Constant(4)),
        PointerOffsetTerm::Constant(4),
    );
    let flat = PointerOffsetTerm::add(base, PointerOffsetTerm::Constant(8));

    assert_eq!(nested, flat);
}

#[test]
fn load_variables_are_congruent_through_ground_index_equalities() {
    // `data[index]` with `index == 0` in scope is the cell `data[0]`: the
    // two load variables are content-addressed by different addresses. They
    // remain distinct in the ordinary equality graph; an explicit atomic
    // derivation retains the address-equality path.
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
        memory.clone(),
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
        !with_index_fact
            .bitvector_terms_equal_from_facts(&indexed_load_variable, &first_load_variable)
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::equal(indexed_load_variable.clone(), first_load_variable.clone()),
        true,
    );
    let derivation = with_index_fact
        .derive_proposition(&goal)
        .expect("the explicit load-address congruence should derive the equality");
    assert!(derivation.load_address_congruence_paths().is_some());
    assert!(derivation.check(&with_index_fact));
    // A different constant index selects a different cell.
    let other = PureFactContext::new().assume_condition(
        ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(7)),
            Bitvector32Term::Constant(1),
        ),
        true,
    );
    assert!(other.derive_proposition(&goal).is_none());

    let other_epoch =
        crate::kernel::intern_c_memory(memory.as_ref().clone().with_call_memory_havoc(
            Variable(8),
            &[CMemoryRange::new(
                Pointer {
                    block: "data".into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )],
            &PureFactContext::new(),
        ));
    let other_epoch_load = crate::kernel::eval::canonical_term(&Bitvector32Term::MemoryLoad(
        other_epoch,
        Box::new(Pointer {
            block: "data".into(),
            offset: PointerOffsetTerm::Constant(0),
        }),
    ));
    let other_epoch_goal = Proposition::ConditionIs(
        ConditionTerm::equal(indexed_load_variable.clone(), other_epoch_load),
        true,
    );
    assert!(
        with_index_fact
            .derive_proposition(&other_epoch_goal)
            .is_none()
    );

    let other_block_load = crate::kernel::eval::canonical_term(&Bitvector32Term::MemoryLoad(
        memory,
        Box::new(Pointer {
            block: "other-data".into(),
            offset: PointerOffsetTerm::Constant(0),
        }),
    ));
    let other_block_goal = Proposition::ConditionIs(
        ConditionTerm::equal(indexed_load_variable, other_block_load),
        true,
    );
    assert!(
        with_index_fact
            .derive_proposition(&other_block_goal)
            .is_none()
    );
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

#[test]
fn symbolic_memory_block_sizes_are_free_and_substitutable() {
    let size_variable = Variable(12_345);
    let block = PointerBlock::Concrete("symbolic-size".to_string());
    let memory = CMemory {
        blocks: std::sync::Arc::new(BTreeMap::from([(
            block.clone(),
            CBlock::with_symbolic_size(Bitvector32Term::Variable(size_variable)),
        )])),
        cells: std::sync::Arc::new(BTreeMap::new()),
        union_cells: std::sync::Arc::new(BTreeMap::new()),
        heap: std::sync::Arc::new(CHeapMemory::default()),
    };

    let mut variables = BTreeSet::new();
    crate::kernel::reasoning::collect_memory_bitvector_variables(&memory, &mut variables);
    assert_eq!(variables, BTreeSet::from([size_variable]));

    let substituted = crate::kernel::reasoning::substitute_bitvector_variable_in_memory(
        &memory,
        size_variable,
        &Bitvector32Term::Constant(24),
    );
    assert_eq!(
        substituted.blocks.get(&block).map(CBlock::size),
        Some(&Bitvector32Term::Constant(24)),
    );
}
