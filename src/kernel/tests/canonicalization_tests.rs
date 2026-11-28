// These tests exercise discovery explicitly through kernel::search::ProofSearch.
use super::*;
use crate::kernel::binary_node;
use crate::kernel::{CompareRelation, MachineIntegerType, OverflowOperation};
use crate::kernel::{MachineCastSpelling, OldMachineTerm, cast_term};

// --- the canonicalization model's production invariants -------------------
// See docs/internals/canonicalization.md.
// Address indices retain shared structural reads. Loaded pointer values still
// use registered observations and defining facts. These tests drive both real
// production boundaries; direct construction alone does not establish them.

/// Walks every pointer offset reachable from a value, collecting the
/// load variables found in scaled positions and rejecting any
/// reachable raw `MemoryLoad` inside an `Int32Scaled` value.
fn collect_offset_load_variables_from_value(
    value: &ProgramValue,
    load_variables: &mut BTreeSet<Variable>,
) {
    match value.numeric_value() {
        ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
        ProgramValue::Void | ProgramValue::Parameter(_) => {}
        crate::kernel::arithmetic_c_value!(term) => {
            collect_offset_load_variables_from_term(term, load_variables);
        }
        ProgramValue::Pointer(pointer) => {
            collect_offset_load_variables_from_offset(&pointer.offset.clone(), load_variables);
        }
    }
}

#[test]
fn floating_values_keep_their_declared_width_and_opaque_payload() {
    let float_pointer = Address::new("float-storage".into(), AddressOffset::constant(0));
    let float_value = ProgramValue::Float32(OldMachineTerm::constant(0x8000_0000));
    let float_memory = SymbolicMemory::new()
        .with_block("float-storage", 4)
        .store(float_pointer.clone(), float_value.clone());
    assert_eq!(float_value.program_type(), ProgramType::Float32);
    assert_eq!(float_value.byte_width(), 4);
    assert!(ProgramType::Float32.accepts(&float_value));
    assert_eq!(
        float_memory.load(&float_pointer),
        ExpressionOutcome::Value(float_value.clone())
    );
    assert_eq!(
        float_memory
            .symbolic_float32_load(&float_pointer)
            .program_type(),
        ProgramType::Float32
    );

    let double_pointer = Address::new("double-storage".into(), AddressOffset::constant(0));
    let double_value =
        ProgramValue::Float64(OldMachineTerm::uint64_constant(0x7ff8_0000_0000_0001));
    let double_memory = SymbolicMemory::new()
        .with_block("double-storage", 8)
        .store(double_pointer.clone(), double_value.clone());
    assert_eq!(double_value.program_type(), ProgramType::Float64);
    assert_eq!(double_value.byte_width(), 8);
    assert!(ProgramType::Float64.accepts(&double_value));
    assert_eq!(
        double_memory.load(&double_pointer),
        ExpressionOutcome::Value(double_value)
    );
    assert_eq!(
        double_memory
            .symbolic_float64_load(&double_pointer)
            .program_type(),
        ProgramType::Float64
    );
}

/// Walks a term in value position: load atoms are legitimate here, but
/// their pointers' offsets must satisfy the no-raw-load invariant.
fn collect_offset_load_variables_from_term(
    term: &OldMachineTerm,
    load_variables: &mut BTreeSet<Variable>,
) {
    match term {
        OldMachineTerm::ThreadHandle(_) | OldMachineTerm::PureApplicationCount(_) => {}
        OldMachineTerm::Constant { .. } | OldMachineTerm::Variable(_) => {}
        OldMachineTerm::MemoryLoad(_, pointer, _) => {
            collect_offset_load_variables_from_offset(&pointer.offset.clone(), load_variables);
        }
        OldMachineTerm::IntegerAddress(pointer, _) => {
            collect_offset_load_variables_from_offset(&pointer.offset.clone(), load_variables);
        }
        crate::kernel::binary_bitvector32_term!(left, right) => {
            collect_offset_load_variables_from_term(left, load_variables);
            collect_offset_load_variables_from_term(right, load_variables);
        }
        OldMachineTerm::Float32Binary { left, right, .. }
        | OldMachineTerm::Float64Binary { left, right, .. } => {
            collect_offset_load_variables_from_term(left, load_variables);
            collect_offset_load_variables_from_term(right, load_variables);
        }
        OldMachineTerm::Float32Negate(value) | OldMachineTerm::Float64Negate(value) => {
            collect_offset_load_variables_from_term(value, load_variables);
        }
        cast_term!(Int64From32, value)
        | OldMachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value,
            ..
        }
        | cast_term!(UInt64From32, value)
        | cast_term!(UInt32From64, value)
        | cast_term!(Int64FromUInt32, value)
        | cast_term!(UInt64FromInt32, value)
        | cast_term!(UInt64FromInt64, value)
        | OldMachineTerm::Unary { operand: value, .. } => {
            collect_offset_load_variables_from_term(value, load_variables);
        }
        crate::kernel::binary_wide_term!(left, right) => {
            collect_offset_load_variables_from_term(left, load_variables);
            collect_offset_load_variables_from_term(right, load_variables);
        }
        OldMachineTerm::If {
            condition: _,
            then_term,
            else_term,
        } => {
            collect_offset_load_variables_from_term(then_term, load_variables);
            collect_offset_load_variables_from_term(else_term, load_variables);
        }
        OldMachineTerm::RangeFold { .. }
        | OldMachineTerm::PureFunctionApplication { .. }
        | OldMachineTerm::ClickFunctionApplication { .. }
        | OldMachineTerm::AlgebraicMatch { .. }
        | OldMachineTerm::BoolCast { .. }
        | OldMachineTerm::IntegerToMachine { .. } => {}
    }
}

fn collect_offset_load_variables_from_offset(
    offset: &AddressOffset,
    load_variables: &mut BTreeSet<Variable>,
) {
    match offset.view() {
        OffsetView::Constant(_) | OffsetView::Variable(_) => {}
        OffsetView::Add(left, right) => {
            collect_offset_load_variables_from_offset(left, load_variables);
            collect_offset_load_variables_from_offset(right, load_variables);
        }
        OffsetView::Int32Scaled { index: value, .. }
        | OffsetView::Int64Scaled { index: value, .. } => {
            assert_scaled_index_free_of_raw_loads(value.structural_value(), load_variables);
        }
    }
}

/// Inside an `Int32Scaled` value no load term may appear; load variables
/// are recorded for the defining-fact check.
fn assert_scaled_index_free_of_raw_loads(
    term: &OldMachineTerm,
    load_variables: &mut BTreeSet<Variable>,
) {
    match term {
        OldMachineTerm::ThreadHandle(_) | OldMachineTerm::PureApplicationCount(_) => {}
        OldMachineTerm::Constant { .. } => {}
        OldMachineTerm::Variable(variable) => {
            if crate::kernel::is_load_variable(variable) {
                load_variables.insert(*variable);
            }
        }
        OldMachineTerm::MemoryLoad(_, _, _) => {
            panic!("production pointer offset contains a raw memory load: {term:?}")
        }
        OldMachineTerm::IntegerAddress(pointer, _) => {
            for value in pointer.offset.native_scaled_values_for_output() {
                assert_scaled_index_free_of_raw_loads(value, load_variables);
            }
        }
        crate::kernel::binary_bitvector32_term!(left, right) => {
            assert_scaled_index_free_of_raw_loads(left, load_variables);
            assert_scaled_index_free_of_raw_loads(right, load_variables);
        }
        cast_term!(Int64From32, value)
        | OldMachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value,
            ..
        }
        | cast_term!(UInt64From32, value)
        | cast_term!(UInt32From64, value)
        | cast_term!(Int64FromUInt32, value)
        | cast_term!(UInt64FromInt32, value)
        | cast_term!(UInt64FromInt64, value)
        | OldMachineTerm::Unary { operand: value, .. } => {
            assert_scaled_index_free_of_raw_loads(value, load_variables);
        }
        crate::kernel::binary_wide_term!(left, right) => {
            assert_scaled_index_free_of_raw_loads(left, load_variables);
            assert_scaled_index_free_of_raw_loads(right, load_variables);
        }
        OldMachineTerm::Float32Negate(value) | OldMachineTerm::Float64Negate(value) => {
            assert_scaled_index_free_of_raw_loads(value, load_variables)
        }
        OldMachineTerm::Float32Binary { left, right, .. }
        | OldMachineTerm::Float64Binary { left, right, .. } => {
            assert_scaled_index_free_of_raw_loads(left, load_variables);
            assert_scaled_index_free_of_raw_loads(right, load_variables);
        }
        OldMachineTerm::If {
            condition: _,
            then_term,
            else_term,
        } => {
            assert_scaled_index_free_of_raw_loads(then_term, load_variables);
            assert_scaled_index_free_of_raw_loads(else_term, load_variables);
        }
        OldMachineTerm::RangeFold { .. }
        | OldMachineTerm::PureFunctionApplication { .. }
        | OldMachineTerm::ClickFunctionApplication { .. }
        | OldMachineTerm::AlgebraicMatch { .. }
        | OldMachineTerm::BoolCast { .. }
        | OldMachineTerm::IntegerToMachine { .. } => {}
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
                && matches!(&fact.proposition(), condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::Equal, left, right: _ }, _)) if (matches!(left.as_ref(), OldMachineTerm::Variable(variable) if variable == load_variable))))
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
    let len_cell = Address::new("len".into(), AddressOffset::constant(0));
    let data = Address::new("data".into(), AddressOffset::constant(0));
    let memory = SymbolicMemory::new()
        .with_block("len", 4)
        .with_block("data", 64);
    let state = ExecutionState::new()
        .with_local("len_ptr", ProgramValue::pointer(len_cell.clone()))
        .with_local("data", ProgramValue::pointer(data))
        .with_memory(memory)
        .with_resource_context(view_memory_context(len_cell.clone(), 0, 1));
    let statement = program_return(crate::kernel::program_expression::add(
        crate::kernel::program_expression::variable("data"),
        crate::kernel::program_expression::typed_load(
            crate::kernel::program_expression::variable("len_ptr"),
            ProgramType::Int32,
        ),
    ));
    let execution =
        prove_symbolic_program_execution_paths(state, statement, PureFactContext::new());

    assert!(!execution.paths().is_empty());
    let mut saw_a_canonical_offset = false;
    for path in execution.paths() {
        let Proposition::ProgramStatementVerifies { outcome, .. } =
            path.theorem().proposition().peel_implications()
        else {
            panic!("execution should prove a statement judgment");
        };
        let StatementOutcome::Return { value, .. } = outcome else {
            continue;
        };
        let ProgramValue::Pointer(pointer) = value.clone().into_native() else {
            panic!("indexing should return a pointer");
        };
        for index in pointer.offset.native_scaled_values_for_output() {
            let OldMachineTerm::MemoryLoad(_, address, kind) = index else {
                panic!("the produced index must retain its structural read");
            };
            assert_eq!(address.as_ref(), &len_cell);
            assert_eq!(*kind, crate::kernel::LoadKind::Int32);
            saw_a_canonical_offset = true;
        }
    }
    assert!(saw_a_canonical_offset, "the loaded index must be retained");
}

/// A pointer loaded from an opaque cell is named by its own read: the
/// value decodes to the cell it was read from, and no raw load enters its
/// offset.
#[test]
fn pointer_loaded_from_an_opaque_cell_is_named_by_its_read() {
    let cell = Address::new("pp".into(), AddressOffset::constant(0));
    let memory = SymbolicMemory::new().with_block("pp", 4);
    let state = ExecutionState::new()
        .with_local("pp", ProgramValue::pointer(cell.clone()))
        .with_memory(memory)
        .with_resource_context(view_memory_context(cell.clone(), 0, 1));
    let statement = program_return(crate::kernel::program_expression::typed_load(
        crate::kernel::program_expression::variable("pp"),
        ProgramType::Int32Pointer,
    ));
    let execution =
        prove_symbolic_program_execution_paths(state, statement, PureFactContext::new());

    assert!(!execution.paths().is_empty());
    let mut saw_a_named_read = false;
    for path in execution.paths() {
        let Proposition::ProgramStatementVerifies { outcome, .. } = path.theorem().proposition()
        else {
            panic!("execution should prove a statement judgment");
        };
        let StatementOutcome::Return { value, .. } = outcome else {
            continue;
        };
        let mut load_variables = BTreeSet::new();
        collect_offset_load_variables_from_value(&value.native(), &mut load_variables);
        assert_load_variables_have_defining_facts(&load_variables, &path.execution_facts());
        if let ProgramValue::Pointer(pointer) = value.clone().into_native()
            && let Some(read) = pointer.address().as_loaded_value()
        {
            assert_eq!(read.defining_address, cell);
            assert_eq!(read.displacement, AddressOffset::constant(0));
            saw_a_named_read = true;
        }
    }
    assert!(
        saw_a_named_read,
        "the loaded pointer should be named by its read of the cell"
    );
}

// --- canonical form: determinism and idempotence --------------------------

fn unresolved_canonicalization_test_load() -> OldMachineTerm {
    let memory = SymbolicMemory::new().with_block("canonical-shapes", 8);
    OldMachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory(memory))),
        Box::new(Address::new(
            "canonical-shapes".into(),
            AddressOffset::constant(0),
        )),
        crate::kernel::LoadKind::Int32,
    )
}

#[test]
fn canonical_term_is_idempotent_for_every_term_shape() {
    macro_rules! machine_binary {
        ($format:ident, $op:ident, $left:expr, $right:expr) => {
            OldMachineTerm::Binary {
                format: MachineIntegerType::$format,
                op: MachineBinaryOp::$op,
                left: Box::new($left),
                right: Box::new($right),
            }
        };
    }
    macro_rules! machine_unary {
        ($format:ident, $op:ident, $value:expr) => {
            OldMachineTerm::Unary {
                format: MachineIntegerType::$format,
                op: MachineUnaryOp::$op,
                operand: Box::new($value),
            }
        };
    }
    macro_rules! unary {
        ($variant:ident, $value:expr) => {
            OldMachineTerm::legacy_cast(MachineCastSpelling::$variant, Box::new($value))
        };
    }

    let load = unresolved_canonicalization_test_load();
    let u32_value = OldMachineTerm::constant(3);
    let i64_value = OldMachineTerm::int64_constant(3);
    let u64_value = OldMachineTerm::uint64_constant(3);
    let terms = vec![
        OldMachineTerm::constant(3),
        OldMachineTerm::int64_constant(3),
        OldMachineTerm::uint64_constant(3),
        OldMachineTerm::Variable(Variable(30_001)),
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
        OldMachineTerm::If {
            condition: Box::new(OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(load.clone()),
                right: Box::new(u32_value.clone()),
            }),
            then_term: Box::new(load.clone()),
            else_term: Box::new(u32_value.clone()),
        },
        OldMachineTerm::RangeFold {
            start: Box::new(load.clone()),
            end: Box::new(u32_value.clone()),
            initial: Box::new(load.clone()),
            accumulator: Variable(30_002),
            item: Variable(30_003),
            body: Box::new(load.clone()),
        },
        OldMachineTerm::PureFunctionApplication {
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
                Box::new(OldMachineTerm::If {
                    condition: Box::new(OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(term),
                        right: Box::new(OldMachineTerm::constant(depth as u32)),
                    }),
                    then_term: Box::new(unresolved_canonicalization_test_load()),
                    else_term: Box::new(OldMachineTerm::constant(depth as u32 + 1)),
                }),
                Box::new(OldMachineTerm::constant(depth as u32 + 2)),
            );
        }

        crate::kernel::memory_history::reset_atomic_canonicalization_term_visits();
        crate::kernel::eval::reset_load_substitution_term_visits();
        let once = crate::kernel::eval::canonical_term(&term);
        let atomic_visits = crate::kernel::memory_history::atomic_canonicalization_term_visits();
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
    let term = OldMachineTerm::Variable(Variable(30_004));
    let canonical = crate::kernel::eval::canonical_term(&term);
    let equal_to_one = PureFactContext::new().assume_condition(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(term.clone()),
            right: Box::new(OldMachineTerm::constant(1)),
        },
        true,
    );
    let equal_to_two = PureFactContext::new().assume_condition(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(term.clone()),
            right: Box::new(OldMachineTerm::constant(2)),
        },
        true,
    );

    let equals = |value| {
        Proposition::condition_is(
            OldConditionTerm::equal(term.clone(), OldMachineTerm::constant(value)),
            true,
        )
    };
    assert!(
        crate::kernel::search::ProofSearch::derive_proposition(&(equal_to_one), &equals(1))
            .is_some()
    );
    assert!(
        crate::kernel::search::ProofSearch::derive_proposition(&(equal_to_two), &equals(2))
            .is_some()
    );
    assert_eq!(crate::kernel::eval::canonical_term(&term), canonical);
    assert_eq!(canonical, term);
}

#[test]
fn canonical_term_resolves_equal_loads_to_one_form() {
    let pointer = Address::new("cells".into(), AddressOffset::constant(0));
    let base = SymbolicMemory::new().with_block("cells", 4);
    // The same unresolved load, read from two states that differ only by
    // a block this load cannot observe.
    let drifted = base.clone().with_block("unrelated", 4);
    let load_at_base = OldMachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory(base.clone()))),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let load_at_drifted = OldMachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory(drifted))),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Int32,
    );

    let canonical = crate::kernel::eval::canonical_term(&load_at_base);
    assert_eq!(
        canonical,
        crate::kernel::eval::canonical_term(&load_at_drifted),
        "representational state drift must not change the canonical form"
    );
    assert!(matches!(canonical, OldMachineTerm::MemoryLoad(..)));
    // Idempotence: the canonical form is its own canonical form.
    assert_eq!(canonical, crate::kernel::eval::canonical_term(&canonical));

    // A load whose cell is materialized resolves to the stored value.
    let stored = base.store(
        pointer.clone(),
        ProgramValue::Int32(OldMachineTerm::constant(7)),
    );
    let resolved = OldMachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory(stored))),
        Box::new(pointer),
        crate::kernel::LoadKind::Int32,
    );
    assert_eq!(
        crate::kernel::eval::canonical_term(&resolved),
        OldMachineTerm::constant(7)
    );
}

#[test]
fn atomic_canonicalization_reaches_loads_in_every_condition_region() {
    let pointer = Address::new("condition-cells".into(), AddressOffset::constant(0));
    let memory = SymbolicMemory::new()
        .with_block("condition-cells", 4)
        .store(
            pointer.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(7)),
        );
    let load = OldMachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory(memory))),
        Box::new(pointer),
        crate::kernel::LoadKind::Int32,
    );
    let overflow = OldMachineTerm::If {
        condition: Box::new(OldConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Add,
            left: Box::new(load.clone()),
            right: Box::new(OldMachineTerm::constant(1)),
        }),
        then_term: Box::new(OldMachineTerm::constant(2)),
        else_term: Box::new(OldMachineTerm::constant(3)),
    };
    let pointer_offset = OldMachineTerm::If {
        condition: Box::new(OldConditionTerm::AddressOffsetEqual(
            Box::new(AddressOffset::scaled_int32_node(load.clone(), 4)),
            Box::new(AddressOffset::constant(28)),
        )),
        then_term: Box::new(OldMachineTerm::constant(4)),
        else_term: Box::new(OldMachineTerm::constant(5)),
    };

    let canonical_overflow = crate::kernel::api::canonicalize_atomic_loads(&overflow);
    let OldMachineTerm::If { condition, .. } = canonical_overflow else {
        panic!("expected conditional term");
    };
    assert!(matches!(
        condition.as_ref(),
        OldConditionTerm::Overflows { format: MachineIntegerType::Int32, op: OverflowOperation::Add, left, right: _ }
            if left.as_ref() == &OldMachineTerm::constant(7)
    ));

    let canonical_pointer_offset = crate::kernel::api::canonicalize_atomic_loads(&pointer_offset);
    let OldMachineTerm::If { condition, .. } = canonical_pointer_offset else {
        panic!("expected conditional term");
    };
    assert!(matches!(
        condition.as_ref(),
        OldConditionTerm::AddressOffsetEqual(left, _)
            if left.as_ref() == &AddressOffset::scaled_int32_node(load.clone(), 4)
    ));
}

#[test]
fn representational_load_equality_holds_beyond_the_former_depth_preflight() {
    let pointer = Address::new("deep-cells".into(), AddressOffset::constant(0));
    let base = SymbolicMemory::new().with_block("deep-cells", 4);
    let drifted = base.clone().with_block("unrelated", 4);
    let mut left = OldMachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory(base))),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let mut right = OldMachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory(drifted))),
        Box::new(pointer),
        crate::kernel::LoadKind::Int32,
    );
    for value in 0..128 {
        left = binary_node!(
            Int32,
            Add,
            Box::new(left),
            Box::new(OldMachineTerm::constant(value))
        );
        right = binary_node!(
            Int32,
            Add,
            Box::new(right),
            Box::new(OldMachineTerm::constant(value))
        );
    }

    assert_eq!(
        crate::kernel::eval::canonical_term(&left),
        crate::kernel::eval::canonical_term(&right),
    );
    assert!(crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(left),
                right: Box::new(right)
            },
            true,
        )
    ));
}

#[test]
fn shared_offsets_retain_state_identity_through_canonicalization() {
    let pointer = Address::new("cells".into(), AddressOffset::constant(0));
    let base = SymbolicMemory::new().with_block("cells", 4);
    let drifted = base.clone().with_block("unrelated", 4);
    let scaled = |memory: SymbolicMemory| {
        AddressOffset::scaled_int32_node(
            OldMachineTerm::read_named(
                ProgramPoint::at(&(crate::kernel::intern_memory(memory))),
                Box::new(pointer.clone()),
                crate::kernel::LoadKind::Int32,
            ),
            4,
        )
    };

    // Equal contents at different states do not make identical terms.
    assert!(!crate::kernel::offsets_have_same_canonical_form(
        &(scaled(base.clone())).clone(),
        &scaled(drifted).clone(),
    ));
    let retained = crate::kernel::eval::canonical_offset_term(&(scaled(base.clone())).clone());
    assert_eq!(retained, scaled(base.clone()));
    // Distinct cells stay distinct.
    let other = Address::new("cells".into(), AddressOffset::constant(4));
    let other_scaled = AddressOffset::scaled_int32_node(
        OldMachineTerm::read_named(
            ProgramPoint::at(&(crate::kernel::intern_memory(base.clone()))),
            Box::new(other),
            crate::kernel::LoadKind::Int32,
        ),
        4,
    );
    assert!(!crate::kernel::offsets_have_same_canonical_form(
        &scaled(base).clone(),
        &other_scaled.clone(),
    ));
}

#[test]
fn canonical_offset_equality_keeps_its_raw_spelling_after_offsets_fold() {
    use crate::kernel::{KernelTerm, OffsetTree, StoredConditionTerm};
    let _session = crate::kernel::VerificationSession::enter();
    let sum = AddressOffset::raw_add(AddressOffset::constant(2), AddressOffset::constant(3));
    let five = AddressOffset::constant(5).into_shared();
    let raw = KernelTerm::address_offset_equal_raw([sum.into_shared(), five.clone()]);
    let expected = KernelTerm::address_offset_equal_raw([five.clone(), five]);
    for truth in [true, false] {
        let source =
            Proposition::condition_is(StoredConditionTerm::from_root(raw.clone()).unwrap(), truth);
        let Proposition::ConditionIs(result, polarity) =
            crate::kernel::canonical_condition_fact(&source)
        else {
            panic!("expected an offset equality")
        };
        assert_eq!(result.root(), Some(&expected));
        assert_eq!(polarity, truth);
        assert!(!raw.has_cached_native_argument());
        assert!(!expected.has_cached_native_argument());
    }
}

#[test]
fn canonical_offset_term_is_complete_and_idempotent_at_multiple_depths() {
    for depth in [64, 128, 256] {
        let mut offset =
            AddressOffset::scaled_int32_node(unresolved_canonicalization_test_load(), 4);
        for _ in 0..depth {
            offset = AddressOffset::raw_add(offset, AddressOffset::constant(1));
        }

        let canonical = crate::kernel::eval::canonical_offset_term(&offset.clone());
        assert_eq!(
            crate::kernel::eval::canonical_offset_term(&canonical),
            canonical,
            "offset canonicalization was not idempotent at depth {depth}",
        );
        let canonical = canonical.clone();
        let mut leaf = &canonical;
        while let crate::kernel::OffsetView::Add(left, _) = leaf.view() {
            leaf = left;
        }
        assert!(
            matches!(leaf.view(),
                crate::kernel::OffsetView::Int32Scaled { index: value, .. }
                    if value.structural_value() == &unresolved_canonicalization_test_load()
            ),
            "the deepest scaled index should retain its read at depth {depth}: {leaf:?}",
        );
    }
}

#[test]
fn pointer_offset_add_coalesces_nested_constant_displacements() {
    let base = AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(17)), 4);
    let nested = AddressOffset::add(
        AddressOffset::add(base.clone(), AddressOffset::constant(4)),
        AddressOffset::constant(4),
    );
    let flat = AddressOffset::add(base, AddressOffset::constant(8));

    assert_eq!(nested, flat);
}

#[test]
fn load_variables_are_congruent_through_ground_index_equalities() {
    // `data[index]` with `index == 0` in scope is the cell `data[0]`: the
    // two structural reads retain different addresses. Congruence in the
    // equality graph identifies them only with the required index equality.
    let memory = crate::kernel::intern_memory(SymbolicMemory::new().with_block("data", 8));
    let index = OldMachineTerm::Variable(Variable(7));
    let indexed = OldMachineTerm::read_named(
        ProgramPoint::at(&memory),
        Box::new(Address::new(
            "data".into(),
            AddressOffset::scaled_int32_node(index.clone(), 4),
        )),
        crate::kernel::LoadKind::Int32,
    );
    let first = OldMachineTerm::read_named(
        ProgramPoint::at(&memory),
        Box::new(Address::new("data".into(), AddressOffset::constant(0))),
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
        OldConditionTerm::equal(index, OldMachineTerm::constant(0)),
        true,
    );
    assert!(
        !with_index_fact.int32_values_known_equal(&indexed_load_variable, &first_load_variable)
    );
    let goal = Proposition::condition_is(
        OldConditionTerm::equal(indexed_load_variable.clone(), first_load_variable.clone()),
        true,
    );
    let derivation =
        crate::kernel::search::ProofSearch::derive_proposition(&(with_index_fact), &goal)
            .expect("the explicit load-address congruence should derive the equality");
    assert!(derivation.check(&with_index_fact));
    assert!(!derivation.check(&without_index_fact));
    // A different constant index selects a different cell.
    let other = PureFactContext::new().assume_condition(
        OldConditionTerm::equal(
            OldMachineTerm::Variable(Variable(7)),
            OldMachineTerm::constant(1),
        ),
        true,
    );
    assert!(crate::kernel::search::ProofSearch::derive_proposition(&(other), &goal).is_none());

    let other_epoch = crate::kernel::intern_memory(memory.as_ref().clone().with_call_memory_havoc(
        Variable(8),
        &[MemoryRange::new(
            Address::new("data".into(), AddressOffset::constant(0)),
            OldMachineTerm::constant(0),
            OldMachineTerm::constant(1),
        )],
        &PureFactContext::new(),
        None,
    ));
    let other_epoch_load = crate::kernel::eval::canonical_term(&OldMachineTerm::read_named(
        ProgramPoint::at(&other_epoch),
        Box::new(Address::new("data".into(), AddressOffset::constant(0))),
        crate::kernel::LoadKind::Int32,
    ));
    let other_epoch_goal = Proposition::condition_is(
        OldConditionTerm::equal(indexed_load_variable.clone(), other_epoch_load),
        true,
    );
    assert!(
        crate::kernel::search::ProofSearch::derive_proposition(
            &(with_index_fact),
            &other_epoch_goal
        )
        .is_none()
    );

    let other_block_load = crate::kernel::eval::canonical_term(&OldMachineTerm::read_named(
        ProgramPoint::at(&memory),
        Box::new(Address::new(
            "other-data".into(),
            AddressOffset::constant(0),
        )),
        crate::kernel::LoadKind::Int32,
    ));
    let other_block_goal = Proposition::condition_is(
        OldConditionTerm::equal(indexed_load_variable, other_block_load),
        true,
    );
    assert!(
        crate::kernel::search::ProofSearch::derive_proposition(
            &(with_index_fact),
            &other_block_goal
        )
        .is_none()
    );
}

#[test]
fn substitution_reaches_through_a_load_variable_with_a_bound_index() {
    // A universal's body contains `p[k]` with the bound `k` inside
    // the load variable's address. Instantiating `k := 0` must reach through
    // the load variable and produce the load variable used by a direct read
    // of `p[0]`.
    let memory = crate::kernel::intern_memory(SymbolicMemory::new().with_block("p", 12));
    let bound = Variable(3_000_000);
    let cell = |offset: AddressOffset| {
        OldMachineTerm::read_named(
            ProgramPoint::at(&memory),
            Box::new(Address::new("p".into(), offset)),
            crate::kernel::LoadKind::Int32,
        )
    };
    let indexed_load_variable = crate::kernel::eval::canonical_term(&cell(
        AddressOffset::scaled_int32_node(OldMachineTerm::Variable(bound), 4),
    ));
    assert!(matches!(
        indexed_load_variable,
        OldMachineTerm::MemoryLoad(..)
    ));
    let instantiated = crate::kernel::reasoning::substitute_bitvector_variable(
        &indexed_load_variable,
        bound,
        &OldMachineTerm::constant(0),
    );
    assert_eq!(
        instantiated,
        crate::kernel::eval::canonical_term(&cell(AddressOffset::constant(0)))
    );
    // Substituting an unrelated variable leaves the load variable untouched.
    assert_eq!(
        crate::kernel::reasoning::substitute_bitvector_variable(
            &indexed_load_variable,
            Variable(3_000_001),
            &OldMachineTerm::constant(0),
        ),
        indexed_load_variable
    );
}

#[test]
fn load_variables_compare_as_loads_under_bounds_pinned_indices() {
    // `p[j]` and `p[2]` are one cell when `j <= 2` and `not (j < 2)`: no
    // recorded equality mentions the index, so the comparison must view the
    // load variables as their loads and decide the addresses from bounds.
    let memory = crate::kernel::intern_memory(SymbolicMemory::new().with_block("p", 12));
    let j = OldMachineTerm::Variable(Variable(7));
    let cell = |offset: AddressOffset| {
        crate::kernel::eval::canonical_term(&OldMachineTerm::read_named(
            ProgramPoint::at(&memory),
            Box::new(Address::new("p".into(), offset)),
            crate::kernel::LoadKind::Int32,
        ))
    };
    let indexed = cell(AddressOffset::scaled_int32_node(j.clone(), 4));
    let third = cell(AddressOffset::constant(8));
    assert_ne!(indexed, third);
    // The index is a free variable of the load variable's denotation.
    let mut variables = BTreeSet::new();
    crate::kernel::reasoning::collect_bitvector_variables(&indexed, &mut variables);
    assert!(variables.contains(&Variable(7)));

    let pinned = PureFactContext::new()
        .assume_condition(
            OldConditionTerm::signed_less_equal(j.clone(), OldMachineTerm::constant(2)),
            true,
        )
        .assume_condition(
            OldConditionTerm::signed_less_than(j.clone(), OldMachineTerm::constant(2)),
            false,
        );
    assert!(pinned.bitvector_terms_proven_equal(&indexed, &third));
    assert!(!PureFactContext::new().bitvector_terms_proven_equal(&indexed, &third));
}

#[test]
fn load_variable_free_variables_include_its_state_cells() {
    // A load variable over a state whose cells mention a loop counter
    // denotes a term mentioning that counter: goal-directed substitutions
    // and other variable-sensitive rules must see it through the load.
    let counter = Variable(11);
    let written = SymbolicMemory::new().with_block("p", 12).store(
        Address::new(
            "p".into(),
            AddressOffset::scaled_int32_node(OldMachineTerm::Variable(counter), 4),
        ),
        ProgramValue::Int32(OldMachineTerm::constant(5)),
    );
    let load_variable = crate::kernel::eval::canonical_term(&OldMachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory(written))),
        Box::new(Address::new("p".into(), AddressOffset::constant(8))),
        crate::kernel::LoadKind::Int32,
    ));
    assert!(matches!(load_variable, OldMachineTerm::MemoryLoad(..)));
    let mut variables = BTreeSet::new();
    crate::kernel::reasoning::collect_bitvector_variables(&load_variable, &mut variables);
    assert!(variables.contains(&counter));
}

#[test]
fn symbolic_memory_block_sizes_are_free_and_substitutable() {
    let size_variable = Variable(12_345);
    let block = AddressBase::Concrete("symbolic-size".to_string());
    let memory = SymbolicMemory {
        construction: None,
        pending_steps: None,
        blocks: std::sync::Arc::new(MemoryBlocks::from_iter([(
            block.clone(),
            MemoryBlock::with_symbolic_size(AllocationSize::int32(OldMachineTerm::Variable(
                size_variable,
            ))),
        )])),
        cells: std::sync::Arc::default(),
        union_cells: std::sync::Arc::default(),
        forgotten: std::sync::Arc::default(),
        heap: std::sync::Arc::new(HeapMemory::default()),
    };

    let mut variables = BTreeSet::new();
    crate::kernel::reasoning::collect_memory_bitvector_variables(&memory, &mut variables);
    assert_eq!(variables, BTreeSet::from([size_variable]));

    let substituted = crate::kernel::reasoning::substitute_bitvector_variable_in_memory(
        &memory,
        size_variable,
        &OldMachineTerm::constant(24),
    );
    assert_eq!(
        substituted.blocks.get(&block).map(MemoryBlock::size),
        Some(&OldMachineTerm::constant(24)),
    );
}

/// A state DAG `depth` levels deep: each level's state is reachable
/// through two distinct cells of the level above, so a rewrite that follows
/// structure instead of state identity visits `2^depth` states while the
/// DAG holds `depth` of them. This is the shape a proof builds when each
/// `unfold` names the cells it exposes and the C then loads through them, one
/// nesting level per unfolded child.
fn nested_state_load(depth: usize) -> OldMachineTerm {
    nested_state_load_named(depth, |load| load)
}

/// [`nested_state_load`] with each cell holding `name(load)`: the load
/// itself, or the load variable that names it.
fn nested_state_load_named(
    depth: usize,
    name: impl Fn(OldMachineTerm) -> OldMachineTerm,
) -> OldMachineTerm {
    let block = AddressBase::Concrete("retained_state-chain".to_string());
    let at = |offset: i64| Address::new(block.clone(), AddressOffset::constant(offset));
    let blocks = std::sync::Arc::new(MemoryBlocks::from_iter([(
        block.clone(),
        MemoryBlock::with_symbolic_size(AllocationSize::int32(OldMachineTerm::constant(
            8 * depth as u32 + 16,
        ))),
    )]));
    let level_memory = |cells| SymbolicMemory {
        construction: None,
        pending_steps: None,
        blocks: blocks.clone(),
        cells: std::sync::Arc::new(cells),
        union_cells: std::sync::Arc::default(),
        forgotten: std::sync::Arc::default(),
        heap: std::sync::Arc::new(HeapMemory::default()),
    };

    let mut memory = level_memory(CellStore::new());
    for level in 0..depth {
        let offset = 8 * level as i64;
        let load = OldMachineTerm::read_named(
            ProgramPoint::at(&(crate::kernel::intern_memory(memory))),
            Box::new(at(offset)),
            crate::kernel::LoadKind::Int32,
        );
        let load = name(load);
        memory = level_memory(CellStore::from_iter([
            (at(offset), ProgramValue::Int32(load.clone())),
            (at(offset + 4), ProgramValue::Int32(load)),
        ]));
    }
    OldMachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory(memory))),
        Box::new(at(8 * depth as i64)),
        crate::kernel::LoadKind::Int32,
    )
}

/// A live memory's variables read from its interned counts are exactly the
/// variables a walk of its every entry finds, through stores, a seeded run,
/// a store into the run and a store that brings back an overwritten value.
#[test]
fn a_live_memorys_counted_variables_are_its_walked_variables() {
    let block = AddressBase::Symbolic(Variable(7_950_000));
    let at = |offset: i64| {
        Address::new(
            block.clone(),
            AddressOffset::add(
                AddressOffset::variable(Variable(7_950_001)),
                AddressOffset::constant(offset),
            ),
        )
    };
    let value = |variable: u64| ProgramValue::Int32(OldMachineTerm::Variable(Variable(variable)));
    let source =
        crate::kernel::intern_memory(SymbolicMemory::new().with_block("counted-source", 64));
    let mut memory = SymbolicMemory::new();
    let mut states = Vec::new();
    for (offset, variable) in [(0, 7_950_010), (4, 7_950_011)] {
        memory = memory.store(at(offset), value(variable));
        states.push(memory.clone());
    }
    memory = memory.with_seeded_cells(at(8), 4, ProgramType::Int32, 0, 1_000, source);
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

/// How many states the named `substitution: state rewrite` operation
/// rebuilt while `operation` ran, beside the run's total deterministic work.
///
/// The count, not the summed span work, is the scaling signal: an operation's
/// work is inclusive of the operations nested inside it, so summing a `depth`
/// deep nest of spans is quadratic even when each state is rebuilt once.
fn state_rewrite_count<R>(operation: impl FnOnce() -> R) -> (R, usize, usize) {
    let ((result, total), events) = crate::instrumentation::collect(|| {
        crate::instrumentation::measure_deterministic_work(operation)
    });
    let rewrites = events
        .into_iter()
        .filter(|event| {
            matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "substitution: state rewrite"
            )
        })
        .count();
    (result, rewrites, total)
}

/// Rewriting one variable must visit each distinct state the term reaches
/// once, not once per path that reaches it.
///
/// A `MemoryLoad` term carries a whole state and a state's cells hold
/// further `MemoryLoad` terms, so these terms are a DAG. Walking it as a tree
/// is what made `mdtests/rb_replace_node_with_children.md` slow: its 96
/// load-variable rewrites cost 965,776 state rebuilds, because three nested
/// `unfold`s each name a cell and the rewritten variable occurs in none of
/// them.
#[test]
fn variable_substitution_visits_each_state_once_per_rewrite() {
    let mut rewrites = Vec::new();
    let mut totals = Vec::new();
    for depth in [2, 4, 8, 16] {
        let goal = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(nested_state_load(depth)),
                right: Box::new(OldMachineTerm::constant(0)),
            },
            true,
        );
        let (rewritten, rewrite_count, total) = state_rewrite_count(|| {
            crate::kernel::reasoning::substitute_bitvector_variable_in_proposition(
                &goal,
                Variable(770_001),
                &OldMachineTerm::constant(1),
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
        "the state-rewrite operation must observe this cost: {rewrites:?}"
    );
    // Four geometric depths, each twice the last. A rewrite performed per
    // reaching path doubles with every added level, so holding adjacent
    // ratios under 3x rejects it without encoding host timing.
    for pair in rewrites.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(3),
            "state rewrites follow reaching paths instead of the state DAG: {rewrites:?} (total work {totals:?})"
        );
    }
    for pair in totals.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(3),
            "substitution work grows faster than the state DAG: {totals:?} (state rewrites {rewrites:?})"
        );
    }
}

/// A pointer cell a state holds materialized is named by the pointer it
/// holds when that value is exactly what a typed load of the cell produces:
/// the structural read of this cell. The version walk cannot cross a loop head's havoc, so a
/// struct field the head copied back would otherwise take a second name.
/// The same value in another cell, or at another pointee width, is not a
/// load of this cell and keeps the walk's name.
#[test]
fn a_materialized_pointer_cell_is_named_by_the_load_it_holds() {
    let field = Address::new("fields".into(), AddressOffset::constant(0));
    let other = Address::new("fields".into(), AddressOffset::constant(8));
    let entry = SymbolicMemory::new().with_block("fields", 16);
    let loaded = crate::kernel::eval::canonical_cell_load(
        &crate::kernel::ProgramPoint::of_memory(&entry),
        &field,
        ProgramType::Int32Pointer,
    );
    let read = Address::loaded(&loaded).expect("the cell's structural read");
    let pointer_at = |value: Address| ProgramValue::typed_pointer(value, ProgramType::Int32Pointer);
    let name_at = |memory: SymbolicMemory, cell: &Address| {
        crate::kernel::eval::canonical_cell_load(
            &crate::kernel::ProgramPoint::of_memory(&memory),
            cell,
            ProgramType::Int32Pointer,
        )
    };

    let held = entry
        .clone()
        .with_block("unrelated", 4)
        .store(field.clone(), pointer_at(read.clone()));
    assert_eq!(
        name_at(held, &field),
        loaded,
        "the cell holds the pointer its own load produced"
    );

    let elsewhere = entry
        .clone()
        .with_block("unrelated", 4)
        .store(other.clone(), pointer_at(read.clone()));
    assert_ne!(
        name_at(elsewhere, &other),
        loaded,
        "another cell holding that pointer is not a load of the first cell"
    );

    let displaced = entry
        .with_block("unrelated", 4)
        .store(field.clone(), pointer_at(read.offset_by_bytes(4)));
    assert_ne!(
        name_at(displaced, &field),
        loaded,
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
    let u = OldMachineTerm::Variable(Variable(7_960_000));
    let scaled = |value: OldMachineTerm| AddressOffset::scaled_int32_node(value, 4);
    let wrapping = scaled(binary_node!(
        Int32,
        Add,
        Box::new(u.clone()),
        Box::new(OldMachineTerm::constant(0x8000_0000)),
    ));
    let offset = AddressOffset::raw_add(wrapping.clone(), AddressOffset::constant(8));
    assert_eq!(
        crate::kernel::reasoning::offset_atoms_and_constant(&offset.clone()),
        (vec![wrapping], 8),
        "the sum inside the scaled index stays one atom"
    );
    assert_eq!(
        crate::kernel::reasoning::offset_atoms_and_constant(
            &(scaled(OldMachineTerm::constant((-3i32) as u32))).clone()
        ),
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
    let block = AddressBase::Symbolic(Variable(7_960_100));
    let source = crate::kernel::intern_memory(SymbolicMemory::new().with_block("wrap-source", 64));
    let base = Address::new(block.clone(), AddressOffset::constant(0));
    let memory = SymbolicMemory::new().with_seeded_cells(base, 4, ProgramType::Int32, 0, 8, source);
    let run = memory
        .cells
        .candidate_runs(&AliasCandidates::of_block(&block))
        .next()
        .expect("the seeded run")
        .clone();
    let bounded = |word: &OldMachineTerm, low: u32| {
        PureFactContext::new()
            .assume_condition(
                OldConditionTerm::signed_less_equal(OldMachineTerm::constant(low), word.clone()),
                true,
            )
            .assume_condition(
                OldConditionTerm::signed_less_than(word.clone(), OldMachineTerm::constant(8)),
                true,
            )
    };
    let store_at = |word: &OldMachineTerm| {
        Address::new(
            block.clone(),
            AddressOffset::scaled_int32_node(word.clone(), 4),
        )
    };

    let wrapping = binary_node!(
        Int32,
        Add,
        Box::new(OldMachineTerm::Variable(Variable(7_960_101))),
        Box::new(OldMachineTerm::constant(0x8000_0000)),
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
        Box::new(OldMachineTerm::Variable(Variable(7_960_102))),
        Box::new(OldMachineTerm::constant(1)),
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
