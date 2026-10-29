// The proposition search these tests exercise is Surface planning now; see
// `src/surface/planning/proposition_search.rs`. The kernel itself never
// calls it, so the tests import the planner explicitly.
use super::*;
use crate::kernel::binary_node;
use crate::kernel::{CompareRelation, MachineIntegerType, OverflowOperation};
use crate::surface::planning::proposition_search::PropositionSearch;

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
    match value.numeric_value() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::Void | CValue::Parameter(_) => {}
        crate::kernel::arithmetic_c_value!(term) => {
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
        | Bitvector32Term::UInt32Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_)
        | Bitvector32Term::Variable(_) => {}
        Bitvector32Term::MemoryLoad(_, pointer, _)
        | Bitvector32Term::PointerAddress(pointer, _) => {
            collect_offset_load_variables_from_offset(&pointer.offset, load_variables);
        }
        crate::kernel::binary_bitvector32_term!(left, right) => {
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
        | Bitvector32Term::MachineIntegerCast { value, .. }
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::UInt32From64(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value)
        | Bitvector32Term::Unary { operand: value, .. } => {
            collect_offset_load_variables_from_term(value, load_variables);
        }
        crate::kernel::binary_wide_term!(left, right) => {
            collect_offset_load_variables_from_term(left, load_variables);
            collect_offset_load_variables_from_term(right, load_variables);
        }
        Bitvector32Term::If {
            condition: _,
            then_term,
            else_term,
        } => {
            collect_offset_load_variables_from_term(then_term, load_variables);
            collect_offset_load_variables_from_term(else_term, load_variables);
        }
        Bitvector32Term::RangeFold { .. }
        | Bitvector32Term::PureFunctionApplication { .. }
        | Bitvector32Term::ClickFunctionApplication { .. }
        | Bitvector32Term::AlgebraicMatch { .. }
        | Bitvector32Term::BoolCast { .. }
        | Bitvector32Term::IntegerToMachine { .. } => {}
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
        | Bitvector32Term::UInt32Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_) => {}
        Bitvector32Term::Variable(variable) => {
            if crate::kernel::is_load_variable(variable) {
                load_variables.insert(*variable);
            }
        }
        Bitvector32Term::MemoryLoad(_, _, _) => {
            panic!("production pointer offset contains a raw memory load: {term:?}")
        }
        Bitvector32Term::PointerAddress(pointer, _) => {
            for value in pointer.offset.scaled_values() {
                assert_scaled_index_free_of_raw_loads(value, load_variables);
            }
        }
        crate::kernel::binary_bitvector32_term!(left, right) => {
            assert_scaled_index_free_of_raw_loads(left, load_variables);
            assert_scaled_index_free_of_raw_loads(right, load_variables);
        }
        Bitvector32Term::Int64From32(value)
        | Bitvector32Term::MachineIntegerCast { value, .. }
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::UInt32From64(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value)
        | Bitvector32Term::Unary { operand: value, .. } => {
            assert_scaled_index_free_of_raw_loads(value, load_variables);
        }
        crate::kernel::binary_wide_term!(left, right) => {
            assert_scaled_index_free_of_raw_loads(left, load_variables);
            assert_scaled_index_free_of_raw_loads(right, load_variables);
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
        Bitvector32Term::RangeFold { .. }
        | Bitvector32Term::PureFunctionApplication { .. }
        | Bitvector32Term::ClickFunctionApplication { .. }
        | Bitvector32Term::AlgebraicMatch { .. }
        | Bitvector32Term::BoolCast { .. }
        | Bitvector32Term::IntegerToMachine { .. } => {}
    }
}

/// Every load variable selected into an offset must carry its exact
/// defining fact in the path's emitted facts.
fn assert_load_variables_have_defining_facts(
    load_variables: &BTreeSet<Variable>,
    facts: &(impl ExecutionFactSource + ?Sized),
) {
    for load_variable in load_variables {
        let defined = facts.fact_iter().any(|fact| {
            crate::kernel::is_load_variable_defining_fact(&fact.proposition)
                && matches!(
                    &fact.proposition,
                    Proposition::ConditionIs(ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::Equal, left, right: _ }, true)
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

/// A pointer loaded from an opaque cell is named by its own read: the
/// value decodes to the cell it was read from, and no raw load enters its
/// offset.
#[test]
fn pointer_loaded_from_an_opaque_cell_is_named_by_its_read() {
    let cell = Pointer {
        block: "pp".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("pp", 4);
    let state = CState::new()
        .with_local("pp", CValue::pointer(cell.clone()))
        .with_memory(memory)
        .with_resource_context(view_memory_context(cell.clone(), 0, 1));
    let statement = c_return(c_typed_load(c_variable("pp"), CType::Int32Pointer));
    let execution = prove_symbolic_c_execution_paths(state, statement, PureFactContext::new());

    assert!(!execution.paths().is_empty());
    let mut saw_a_named_read = false;
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
        if let CValue::Pointer(pointer) = value
            && let Some(read) = pointer.pointer().as_loaded_value()
        {
            assert_eq!(read.defining_address, cell);
            assert_eq!(read.displacement, PointerOffsetTerm::Constant(0));
            saw_a_named_read = true;
        }
    }
    assert!(
        saw_a_named_read,
        "the loaded pointer should be named by its read of the cell"
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
        crate::kernel::LoadKind::Int32,
    )
}

#[test]
fn canonical_term_is_idempotent_for_every_term_shape() {
    macro_rules! machine_binary {
        ($format:ident, $op:ident, $left:expr, $right:expr) => {
            Bitvector32Term::Binary {
                format: MachineIntegerType::$format,
                op: MachineBinaryOp::$op,
                left: Box::new($left),
                right: Box::new($right),
            }
        };
    }
    macro_rules! machine_unary {
        ($format:ident, $op:ident, $value:expr) => {
            Bitvector32Term::Unary {
                format: MachineIntegerType::$format,
                op: MachineUnaryOp::$op,
                operand: Box::new($value),
            }
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
        machine_binary!(Int32, Add, load.clone(), u32_value.clone()),
        machine_binary!(Int32, Subtract, load.clone(), u32_value.clone()),
        machine_binary!(Int32, Multiply, load.clone(), u32_value.clone()),
        machine_binary!(Int32, Divide, load.clone(), u32_value.clone()),
        machine_binary!(UInt32, Divide, load.clone(), u32_value.clone()),
        machine_binary!(Int32, Remainder, load.clone(), u32_value.clone()),
        machine_binary!(UInt32, Remainder, load.clone(), u32_value.clone()),
        machine_binary!(Int32, ShiftLeft, load.clone(), u32_value.clone()),
        machine_binary!(Int32, ShiftRight, load.clone(), u32_value.clone()),
        machine_binary!(UInt32, ShiftRight, load.clone(), u32_value.clone()),
        machine_binary!(Int32, BitwiseAnd, load.clone(), u32_value.clone()),
        machine_binary!(Int32, BitwiseOr, load.clone(), u32_value.clone()),
        machine_binary!(Int32, BitwiseXor, load.clone(), u32_value.clone()),
        machine_unary!(Int32, BitwiseNot, load.clone()),
        Bitvector32Term::If {
            condition: Box::new(ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(load.clone()),
                right: Box::new(u32_value.clone()),
            }),
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
        unary!(UInt32From64, load.clone()),
        unary!(Int64FromUInt32, load.clone()),
        unary!(UInt64FromInt32, load.clone()),
        unary!(UInt64FromInt64, load.clone()),
        machine_unary!(Int64, BitwiseNot, load.clone()),
        machine_unary!(UInt64, BitwiseNot, load.clone()),
        machine_binary!(Int64, Add, load.clone(), i64_value.clone()),
        machine_binary!(Int64, Subtract, load.clone(), i64_value.clone()),
        machine_binary!(Int64, Multiply, load.clone(), i64_value.clone()),
        machine_binary!(Int64, Divide, load.clone(), i64_value.clone()),
        machine_binary!(Int64, Remainder, load.clone(), i64_value.clone()),
        machine_binary!(Int64, ShiftLeft, load.clone(), i64_value.clone()),
        machine_binary!(Int64, ShiftRight, load.clone(), i64_value.clone()),
        machine_binary!(Int64, BitwiseAnd, load.clone(), i64_value.clone()),
        machine_binary!(Int64, BitwiseOr, load.clone(), i64_value.clone()),
        machine_binary!(Int64, BitwiseXor, load.clone(), i64_value.clone()),
        machine_binary!(UInt64, Add, load.clone(), u64_value.clone()),
        machine_binary!(UInt64, Subtract, load.clone(), u64_value.clone()),
        machine_binary!(UInt64, Multiply, load.clone(), u64_value.clone()),
        machine_binary!(UInt64, Divide, load.clone(), u64_value.clone()),
        machine_binary!(UInt64, Remainder, load.clone(), u64_value.clone()),
        machine_binary!(UInt64, ShiftLeft, load.clone(), u64_value.clone()),
        machine_binary!(UInt64, ShiftRight, load.clone(), u64_value.clone()),
        machine_binary!(UInt64, BitwiseAnd, load.clone(), u64_value.clone()),
        machine_binary!(UInt64, BitwiseOr, load.clone(), u64_value.clone()),
        machine_binary!(UInt64, BitwiseXor, load, u64_value),
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
            term = binary_node!(
                Int32,
                Add,
                Box::new(Bitvector32Term::If {
                    condition: Box::new(ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(term),
                        right: Box::new(Bitvector32Term::Constant(depth as u32)),
                    }),
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
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(term.clone()),
            right: Box::new(Bitvector32Term::Constant(1)),
        },
        true,
    );
    let equal_to_two = PureFactContext::new().assume_condition(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(term.clone()),
            right: Box::new(Bitvector32Term::Constant(2)),
        },
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
        crate::kernel::LoadKind::Int32,
    );
    let load_at_drifted = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(drifted),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Int32,
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
    let resolved = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(stored),
        Box::new(pointer),
        crate::kernel::LoadKind::Int32,
    );
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
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory),
        Box::new(pointer),
        crate::kernel::LoadKind::Int32,
    );
    let overflow = Bitvector32Term::If {
        condition: Box::new(ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Add,
            left: Box::new(load.clone()),
            right: Box::new(Bitvector32Term::Constant(1)),
        }),
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
        ConditionTerm::Overflows { format: MachineIntegerType::Int32, op: OverflowOperation::Add, left, right: _ }
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
        crate::kernel::LoadKind::Int32,
    );
    let mut right = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(drifted),
        Box::new(pointer),
        crate::kernel::LoadKind::Int32,
    );
    for value in 0..128 {
        left = binary_node!(
            Int32,
            Add,
            Box::new(left),
            Box::new(Bitvector32Term::Constant(value))
        );
        right = binary_node!(
            Int32,
            Add,
            Box::new(right),
            Box::new(Bitvector32Term::Constant(value))
        );
    }

    assert_eq!(
        crate::kernel::eval::canonical_term(&left),
        crate::kernel::eval::canonical_term(&right),
    );
    assert!(PureFactContext::new().proves(&Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(left),
            right: Box::new(right)
        },
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
            crate::kernel::LoadKind::Int32,
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
            crate::kernel::LoadKind::Int32,
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
        crate::kernel::LoadKind::Int32,
    );
    let first = Bitvector32Term::MemoryLoad(
        memory.clone(),
        Box::new(Pointer {
            block: "data".into(),
            offset: PointerOffsetTerm::Constant(0),
        }),
        crate::kernel::LoadKind::Int32,
    );
    let indexed_load_variable = crate::kernel::eval::canonical_term(&indexed);
    let first_load_variable = crate::kernel::eval::canonical_term(&first);
    assert_ne!(
        indexed_load_variable, first_load_variable,
        "distinct addresses take distinct load variables"
    );

    let without_index_fact = PureFactContext::new();
    assert!(
        !without_index_fact.int32_values_known_equal(&indexed_load_variable, &first_load_variable)
    );

    let with_index_fact = PureFactContext::new().assume_condition(
        ConditionTerm::equal(index, Bitvector32Term::Constant(0)),
        true,
    );
    assert!(
        !with_index_fact.int32_values_known_equal(&indexed_load_variable, &first_load_variable)
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
            None,
        ));
    let other_epoch_load = crate::kernel::eval::canonical_term(&Bitvector32Term::MemoryLoad(
        other_epoch,
        Box::new(Pointer {
            block: "data".into(),
            offset: PointerOffsetTerm::Constant(0),
        }),
        crate::kernel::LoadKind::Int32,
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
        crate::kernel::LoadKind::Int32,
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
            crate::kernel::LoadKind::Int32,
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
            crate::kernel::LoadKind::Int32,
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
    // denotes a term mentioning that counter: goal-directed substitutions
    // and other variable-sensitive rules must see it through the load.
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
        crate::kernel::LoadKind::Int32,
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
        construction: None,
        blocks: std::sync::Arc::new(SnapshotMap::from_iter([(
            block.clone(),
            CBlock::with_symbolic_size(Bitvector32Term::Variable(size_variable)),
        )])),
        cells: std::sync::Arc::default(),
        union_cells: std::sync::Arc::default(),
        forgotten: std::sync::Arc::default(),
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

/// A snapshot DAG `depth` levels deep: each level's snapshot is reachable
/// through two distinct cells of the level above, so a rewrite that follows
/// structure instead of snapshot identity visits `2^depth` snapshots while the
/// DAG holds `depth` of them. This is the shape a proof builds when each
/// `unfold` names the cells it exposes and the C then loads through them, one
/// nesting level per unfolded child.
fn nested_snapshot_load(depth: usize) -> Bitvector32Term {
    nested_snapshot_load_named(depth, |load| load)
}

/// [`nested_snapshot_load`] with each cell holding `name(load)`: the load
/// itself, or the load variable that names it.
fn nested_snapshot_load_named(
    depth: usize,
    name: impl Fn(Bitvector32Term) -> Bitvector32Term,
) -> Bitvector32Term {
    let block = PointerBlock::Concrete("snapshot-chain".to_string());
    let at = |offset: i64| Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::Constant(offset),
    };
    let blocks = std::sync::Arc::new(SnapshotMap::from_iter([(
        block.clone(),
        CBlock::with_symbolic_size(Bitvector32Term::Constant(8 * depth as u32 + 16)),
    )]));
    let level_memory = |cells| CMemory {
        construction: None,
        blocks: blocks.clone(),
        cells: std::sync::Arc::new(cells),
        union_cells: std::sync::Arc::default(),
        forgotten: std::sync::Arc::default(),
        heap: std::sync::Arc::new(CHeapMemory::default()),
    };

    let mut memory = level_memory(CellStore::new());
    for level in 0..depth {
        let offset = 8 * level as i64;
        let load = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(memory),
            Box::new(at(offset)),
            crate::kernel::LoadKind::Int32,
        );
        let load = name(load);
        memory = level_memory(CellStore::from_iter([
            (at(offset), CValue::Int32(load.clone())),
            (at(offset + 4), CValue::Int32(load)),
        ]));
    }
    Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory),
        Box::new(at(8 * depth as i64)),
        crate::kernel::LoadKind::Int32,
    )
}

/// A symbolic static array of pointers holds, at each element, a fresh
/// symbolic pointer named by that element's own load, so substituting that
/// name rewrites that element and no other. The elements the run's
/// representatives stand for are unchanged by it, so the run has to single
/// the element out rather than keep itself whole.
#[test]
fn a_pointer_substitution_rewrites_the_one_symbolic_array_element_it_names() {
    let block = PointerBlock::Concrete("symbolic-pointer-array".to_string());
    let at = |offset: i64| Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::Constant(offset),
    };
    let elements = 100u32;
    let width = CType::Int32Pointer.byte_width();
    let size = width * elements;
    let source = crate::kernel::intern_c_memory(
        CMemory::new().with_block_without_derivation(block.clone(), size),
    );
    let Ok(memory) = CMemory::new()
        .with_block("symbolic-pointer-array", size)
        .with_symbolic_storage_run(at(0), CType::Int32Pointer, elements, source)
    else {
        panic!("a symbolic array over a fresh block is one run");
    };
    let element = |memory: &CMemory, index: i64| {
        memory
            .cells
            .get(&at(index * i64::from(width)))
            .expect("every element holds a cell")
    };
    let named = match element(&memory, 50) {
        CValue::Pointer(pointer) => match pointer.pointer().block {
            PointerBlock::Symbolic(variable) => variable,
            ref other => panic!("an element points into its own symbolic block, not {other:?}"),
        },
        other => panic!("an element holds a pointer, not {other:?}"),
    };
    let target = CMemory::global_pointer("target");
    let substituted =
        crate::kernel::reasoning::substitute_pointer_variable_in_memory(&memory, named, &target);
    assert_eq!(
        element(&substituted, 50),
        match element(&memory, 50) {
            CValue::Pointer(pointer) => CValue::Pointer(pointer.with_address(target)),
            _ => unreachable!(),
        }
    );
    for index in [0, 1, 49, 51, 99] {
        assert_eq!(element(&substituted, index), element(&memory, index));
    }
}

/// A live memory's variables read from its interned counts are exactly the
/// variables a walk of its every entry finds, through stores, a seeded run,
/// a store into the run and a store that brings back an overwritten value.
#[test]
fn a_live_memorys_counted_variables_are_its_walked_variables() {
    let block = PointerBlock::Symbolic(Variable(7_950_000));
    let at = |offset: i64| Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::Variable(Variable(7_950_001)),
            PointerOffsetTerm::Constant(offset),
        ),
    };
    let value = |variable: u64| CValue::Int32(Bitvector32Term::Variable(Variable(variable)));
    let source = crate::kernel::intern_c_memory(CMemory::new().with_block("counted-source", 64));
    let mut memory = CMemory::new();
    let mut states = Vec::new();
    for (offset, variable) in [(0, 7_950_010), (4, 7_950_011)] {
        memory = memory.store(at(offset), value(variable));
        states.push(memory.clone());
    }
    memory = memory.with_seeded_cells(at(8), 4, CType::Int32, 0, 1_000, source);
    states.push(memory.clone());
    for (offset, variable) in [(16, 7_950_012), (0, 7_950_013), (0, 7_950_010)] {
        memory = memory.store(at(offset), value(variable));
        states.push(memory.clone());
    }
    crate::kernel::reasoning::variable_collection::clear_shared_memory_variables();
    for (step, state) in states.iter().enumerate() {
        assert!(
            crate::kernel::primitives::interned_storage_of(state).is_some(),
            "step {step}: a derived memory carries its interned storage"
        );
        let mut counted = BTreeSet::new();
        crate::kernel::reasoning::collect_memory_bitvector_variables(state, &mut counted);
        let mut walked = BTreeSet::new();
        crate::kernel::reasoning::variable_collection::collect_memory_bitvector_variables_whole(
            state,
            &mut walked,
        );
        assert_eq!(counted, walked, "step {step}");
    }
}

/// How many snapshots the named `substitution: snapshot rewrite` operation
/// rebuilt while `operation` ran, beside the run's total deterministic work.
///
/// The count, not the summed span work, is the scaling signal: an operation's
/// work is inclusive of the operations nested inside it, so summing a `depth`
/// deep nest of spans is quadratic even when each snapshot is rebuilt once.
fn snapshot_rewrite_count<R>(operation: impl FnOnce() -> R) -> (R, usize, usize) {
    let ((result, total), events) = crate::instrumentation::collect(|| {
        crate::instrumentation::measure_deterministic_work(operation)
    });
    let rewrites = events
        .into_iter()
        .filter(|event| {
            matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "substitution: snapshot rewrite"
            )
        })
        .count();
    (result, rewrites, total)
}

/// Rewriting one variable must visit each distinct snapshot the term reaches
/// once, not once per path that reaches it.
///
/// A `MemoryLoad` term carries a whole snapshot and a snapshot's cells hold
/// further `MemoryLoad` terms, so these terms are a DAG. Walking it as a tree
/// is what made `mdtests/rb_replace_node_with_children.md` slow: its 96
/// load-variable rewrites cost 965,776 snapshot rebuilds, because three nested
/// `unfold`s each name a cell and the rewritten variable occurs in none of
/// them.
#[test]
fn variable_substitution_visits_each_snapshot_once_per_rewrite() {
    let mut rewrites = Vec::new();
    let mut totals = Vec::new();
    for depth in [2, 4, 8, 16] {
        let goal = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(nested_snapshot_load(depth)),
                right: Box::new(Bitvector32Term::Constant(0)),
            },
            true,
        );
        let (rewritten, rewrite_count, total) = snapshot_rewrite_count(|| {
            crate::kernel::reasoning::substitute_bitvector_variable_in_proposition(
                &goal,
                Variable(770_001),
                &Bitvector32Term::Constant(1),
            )
        });
        // The rewritten variable occurs nowhere, so every visit is pure
        // walking and the goal must come back unchanged.
        assert_eq!(rewritten, goal, "depth {depth} rewrite changed the goal");
        rewrites.push(rewrite_count);
        totals.push(total);
    }

    assert!(
        rewrites[0] > 0,
        "the snapshot-rewrite operation must observe this cost: {rewrites:?}"
    );
    // Four geometric depths, each twice the last. A rewrite performed per
    // reaching path doubles with every added level, so holding adjacent
    // ratios under 3x rejects it without encoding host timing.
    for pair in rewrites.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(3),
            "snapshot rewrites follow reaching paths instead of the snapshot DAG: {rewrites:?} (total work {totals:?})"
        );
    }
    for pair in totals.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(3),
            "substitution work grows faster than the snapshot DAG: {totals:?} (snapshot rewrites {rewrites:?})"
        );
    }
}

/// A pointer cell a snapshot holds materialized is named by the pointer it
/// holds when that value is exactly what a typed load of the cell produces:
/// the cell's block, offset `v * 4` for an `int32*`, and `v` registered as a
/// load of this cell. The version walk cannot cross a loop head's havoc, so a
/// struct field the head copied back would otherwise take a second name.
/// The same value in another cell, or at another pointee width, is not a
/// load of this cell and keeps the walk's name.
#[test]
fn a_materialized_pointer_cell_is_named_by_the_load_it_holds() {
    let field = Pointer {
        block: "fields".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let other = Pointer {
        block: "fields".into(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let entry = CMemory::new().with_block("fields", 16);
    let Bitvector32Term::Variable(loaded) = crate::kernel::canonical_form_of_load(
        intern_c_memory(entry.clone()),
        field.clone(),
        crate::kernel::LoadKind::Int32,
    ) else {
        panic!("a load of an opaque cell is named by a load variable");
    };
    let read = Pointer::loaded(&Bitvector32Term::Variable(loaded))
        .expect("the cell's load names its read");
    let pointer_at = |value: Pointer| CValue::typed_pointer(value, CType::Int32Pointer);
    let name_at = |memory: CMemory, cell: &Pointer| {
        crate::kernel::canonical_form_of_load(
            intern_c_memory(memory),
            cell.clone(),
            crate::kernel::LoadKind::Int32,
        )
    };

    let held = entry
        .clone()
        .with_block("unrelated", 4)
        .store(field.clone(), pointer_at(read.clone()));
    assert_eq!(
        name_at(held, &field),
        Bitvector32Term::Variable(loaded),
        "the cell holds the pointer its own load produced"
    );

    let elsewhere = entry
        .clone()
        .with_block("unrelated", 4)
        .store(other.clone(), pointer_at(read.clone()));
    assert_ne!(
        name_at(elsewhere, &other),
        Bitvector32Term::Variable(loaded),
        "another cell holding that pointer is not a load of the first cell"
    );

    let displaced = entry
        .with_block("unrelated", 4)
        .store(field.clone(), pointer_at(read.offset_by_bytes(4)));
    assert_ne!(
        name_at(displaced, &field),
        Bitvector32Term::Variable(loaded),
        "a pointer displaced from the cell's read is not what a typed load of the cell produces"
    );
}

// --- a scaled index is one atom whole ---------------------------------------
// See `mdtests/a_converted_unsigned_index_sum_is_not_split.md`.

/// `Int32Scaled { i + c }` is `sext(i + c) * w`, not `sext(i) * w + c * w`:
/// the split keeps a non-constant scaled index whole, and only a constant
/// scaled index (at its signed value) or a `Constant` summand joins the shift.
#[test]
fn a_scaled_index_sum_is_one_atom_and_a_constant_index_is_a_shift() {
    let u = Bitvector32Term::Variable(Variable(7_960_000));
    let scaled = |value: Bitvector32Term| PointerOffsetTerm::Int32Scaled {
        value: Box::new(value),
        byte_width: 4,
    };
    let wrapping = scaled(binary_node!(
        Int32,
        Add,
        Box::new(u.clone()),
        Box::new(Bitvector32Term::Constant(0x8000_0000)),
    ));
    let offset = PointerOffsetTerm::Add(
        Box::new(wrapping.clone()),
        Box::new(PointerOffsetTerm::Constant(8)),
    );
    assert_eq!(
        crate::kernel::reasoning::offset_atoms_and_constant(&offset),
        (vec![wrapping], 8),
        "the sum inside the scaled index stays one atom"
    );
    assert_eq!(
        crate::kernel::reasoning::offset_atoms_and_constant(&scaled(Bitvector32Term::Constant(
            (-3i32) as u32
        ))),
        (Vec::new(), -12),
        "a constant scaled index is its signed value times the width"
    );
}

/// A run of eight `int32` slots and a store at `a[w]` whose word `w` is
/// `u + 2^31`, bounded to `0 <= w < 8`. The split read the store as the atom
/// `u` (interval `[INT_MIN, INT_MAX]`) plus `INT_MIN` elements, whose whole
/// window lies below the run, and kept every slot; `w` may be any element.
/// The signed neighbour `i + 1`, bounded by its own facts, still places the
/// store off element 0.
#[test]
fn a_store_through_a_wrapping_index_sum_is_placed_by_the_word_itself() {
    use crate::kernel::primitives::{AliasCandidates, SlotSet};
    let block = PointerBlock::Symbolic(Variable(7_960_100));
    let source = crate::kernel::intern_c_memory(CMemory::new().with_block("wrap-source", 64));
    let base = Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_seeded_cells(base, 4, CType::Int32, 0, 8, source);
    let run = memory
        .cells
        .candidate_runs(&AliasCandidates::of_block(&block))
        .next()
        .expect("the seeded run")
        .clone();
    let bounded = |word: &Bitvector32Term, low: u32| {
        PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(low), word.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(word.clone(), Bitvector32Term::Constant(8)),
                true,
            )
    };
    let store_at = |word: &Bitvector32Term| Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(word.clone()),
            byte_width: 4,
        },
    };

    let wrapping = binary_node!(
        Int32,
        Add,
        Box::new(Bitvector32Term::Variable(Variable(7_960_101))),
        Box::new(Bitvector32Term::Constant(0x8000_0000)),
    );
    let (kept, _) = crate::kernel::reasoning::run_slots_kept_by_store(
        &run,
        &store_at(&wrapping),
        4,
        &bounded(&wrapping, 0),
    );
    assert_eq!(
        kept,
        SlotSet::Except(0, 8),
        "all possibly written slots are forgotten"
    );

    let neighbour = binary_node!(
        Int32,
        Add,
        Box::new(Bitvector32Term::Variable(Variable(7_960_102))),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let (kept, _) = crate::kernel::reasoning::run_slots_kept_by_store(
        &run,
        &store_at(&neighbour),
        4,
        &bounded(&neighbour, 1),
    );
    assert_eq!(
        kept,
        SlotSet::Except(1, 8),
        "element 0 is kept by the bound"
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/canonicalization_tests.rs");
}
