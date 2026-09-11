//! Regression coverage for registered-load capture and nested reminting.
//!
//! These tests deliberately use checked `TermRewrite` entry points; they do
//! not inspect the collector's private summaries directly.

use super::*;
use crate::kernel::{
    CMemory, IntegerRangeFoldIndex, IntegerTerm, MachineIntegerType, Pointer, PointerBlock,
    PointerOffsetTerm, SharedCMemory, SharedIntegerRangeEndpoint, SharedIntegerTerm,
    SharedMachineIntegerTerm, Term, Variable,
};
use std::collections::BTreeMap;

fn memory() -> SharedCMemory {
    crate::kernel::intern_c_memory(CMemory::new().with_block("registered-load-capture", 64))
}

fn exact_load(memory: &SharedCMemory, pointer: &Pointer) -> Variable {
    crate::kernel::eval::load_variable_for_exact_cell(memory, pointer)
}

fn int32_fold(accumulator: Variable, item: Variable, body: IntegerTerm) -> IntegerTerm {
    IntegerTerm::range_fold(
        IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(0)),
            end: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(1)),
        },
        IntegerTerm::constant_i64(0),
        accumulator,
        item,
        body,
    )
}

fn integer_fold(accumulator: Variable, item: Variable, body: IntegerTerm) -> IntegerTerm {
    IntegerTerm::range_fold(
        IntegerRangeFoldIndex::Integer {
            start: IntegerTerm::constant_i64(0).into(),
            end: IntegerTerm::constant_i64(1).into(),
        },
        IntegerTerm::constant_i64(0),
        accumulator,
        item,
        body,
    )
}

fn machine_variable(variable: Variable) -> IntegerTerm {
    IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
        MachineIntegerType::Int32,
        Bitvector32Term::Variable(variable),
    ))
}

#[test]
fn checked_c_substitution_reserves_free_integer_in_registered_load_pointer() {
    let memory = memory();
    let source = Variable(3_210_000);
    let free_integer = Variable(3_210_001);
    let accumulator = Variable(3_210_002);
    let inner_load = exact_load(
        &memory,
        &Pointer {
            block: PointerBlock::Concrete("registered-load-capture".into()),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::IntegerToMachine {
                    value: SharedIntegerTerm::from(IntegerTerm::Variable(free_integer)),
                    destination: MachineIntegerType::Int32,
                }),
                byte_width: 4,
            },
        },
    );
    let load = exact_load(
        &memory,
        &Pointer {
            block: PointerBlock::Concrete("registered-load-capture".into()),
            offset: PointerOffsetTerm::Variable(inner_load),
        },
    );
    let fold = integer_fold(accumulator, free_integer, machine_variable(source));
    let source_term = Bitvector32Term::Variable(source);
    let replacement_term = Bitvector32Term::Add(
        Box::new(Bitvector32Term::Variable(load)),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let mut rewrite = TermRewrite::for_bits_checked(&source_term, &replacement_term);
    rewrite.enable_registered_load_resolution();
    let output = rewrite.term(&Term::Integer(fold));
    assert!(!rewrite.integer_work_exhausted);
    assert!(!rewrite.unsupported_integer_scope);

    let Term::Integer(IntegerTerm::RangeFold { item, body, .. }) = output else {
        panic!("checked substitution dropped the Integer fold")
    };
    assert_ne!(
        item, free_integer,
        "free Integer pointer input was captured"
    );
    assert!(matches!(body.as_ref(), IntegerTerm::Machine(machine)
        if machine.value() == &replacement_term));
    let (_, pointer) = crate::kernel::eval::registered_load_for_variable(&inner_load)
        .expect("replacement load must retain its defining pointer");
    assert!(matches!(pointer.offset,
        PointerOffsetTerm::Int32Scaled { value, .. }
            if matches!(value.as_ref(), Bitvector32Term::IntegerToMachine { value, .. }
                if matches!(value.as_ref(), IntegerTerm::Variable(variable)
                    if *variable == free_integer))));
}

#[test]
fn checked_c_substitution_reserves_free_c_in_registered_load_pointer() {
    let memory = memory();
    let source = Variable(3_220_000);
    let free_c = Variable(3_220_001);
    let accumulator = Variable(3_220_002);
    let load = exact_load(
        &memory,
        &Pointer {
            block: PointerBlock::Concrete("registered-load-capture".into()),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(free_c)),
                byte_width: 4,
            },
        },
    );
    let fold = int32_fold(accumulator, free_c, machine_variable(source));
    let source_term = Bitvector32Term::Variable(source);
    let replacement_term = Bitvector32Term::Variable(load);
    let mut rewrite = TermRewrite::for_bits_checked(&source_term, &replacement_term);
    rewrite.enable_registered_load_resolution();
    let output = rewrite.term(&Term::Integer(fold));
    assert!(!rewrite.integer_work_exhausted);
    assert!(!rewrite.unsupported_integer_scope);

    let Term::Integer(IntegerTerm::RangeFold { item, body, .. }) = output else {
        panic!("checked substitution dropped the C fold")
    };
    assert_ne!(item, free_c, "free C pointer input was captured");
    assert!(matches!(body.as_ref(), IntegerTerm::Machine(machine)
        if machine.value() == &Bitvector32Term::Variable(load)));
    let (_, pointer) = crate::kernel::eval::registered_load_for_variable(&load)
        .expect("replacement load must retain its defining pointer");
    assert!(matches!(pointer.offset,
        PointerOffsetTerm::Int32Scaled { value, .. }
            if matches!(value.as_ref(), Bitvector32Term::Variable(variable)
                if *variable == free_c)));
}

#[test]
fn checked_registered_load_rewrite_remints_nested_direct_offset() {
    let memory = memory();
    let source = Variable(3_230_000);
    let inner_pointer = Pointer {
        block: PointerBlock::Concrete("registered-load-capture".into()),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(source)),
            byte_width: 4,
        },
    };
    let inner = exact_load(&memory, &inner_pointer);
    let outer = exact_load(
        &memory,
        &Pointer {
            block: PointerBlock::Concrete("registered-load-capture".into()),
            offset: PointerOffsetTerm::Variable(inner),
        },
    );
    let input = Term::Integer(machine_variable(outer));
    let source_term = Bitvector32Term::Variable(source);
    let replacement_term = Bitvector32Term::Constant(9);
    let mut rewrite = TermRewrite::for_bits_checked(&source_term, &replacement_term);
    rewrite.enable_registered_load_resolution();
    let output = rewrite.term(&input);
    assert!(!rewrite.integer_work_exhausted);
    assert!(!rewrite.unsupported_integer_scope);

    let Term::Integer(IntegerTerm::Machine(machine)) = output else {
        panic!("nested registered load changed the Integer carrier")
    };
    let Bitvector32Term::Variable(rewritten_outer) = machine.value() else {
        panic!("nested registered load expanded into a memory tree")
    };
    assert_ne!(*rewritten_outer, outer);
    let (outer_memory, outer_pointer) =
        crate::kernel::eval::registered_load_for_variable(rewritten_outer)
            .expect("outer remint must remain registered");
    assert_eq!(outer_memory, memory);
    let PointerOffsetTerm::Variable(rewritten_inner) = outer_pointer.offset else {
        panic!("direct nested offset was not retained")
    };
    assert_ne!(rewritten_inner, inner);
    let (inner_memory, inner_pointer) =
        crate::kernel::eval::registered_load_for_variable(&rewritten_inner)
            .expect("inner remint must remain registered");
    assert_eq!(inner_memory, memory);
    assert_eq!(
        inner_pointer.offset,
        PointerOffsetTerm::Constant(36),
        "the reminted inner load keeps the canonical byte offset (9 * 4)"
    );
}

#[test]
fn checked_integer_binding_rewrites_registered_load_at_exact_snapshot() {
    let memory = memory();
    let source = Variable(3_240_000);
    let pointer = Pointer {
        block: PointerBlock::Concrete("registered-load-capture".into()),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::IntegerToMachine {
                value: SharedIntegerTerm::from(IntegerTerm::var(source)),
                destination: MachineIntegerType::Int32,
            }),
            byte_width: 4,
        },
    };
    let load = exact_load(&memory, &pointer);
    let input = Term::Integer(machine_variable(load));
    let c_replacements = BTreeMap::new();
    let integer_replacements = BTreeMap::from([(source, IntegerTerm::constant_i64(9))]);
    let algebraic_replacements = BTreeMap::new();
    let mut rewrite = TermRewrite::for_checked_typed_variables(
        &c_replacements,
        &integer_replacements,
        &algebraic_replacements,
    );
    rewrite.enable_registered_load_resolution();
    let output = rewrite.term(&input);
    assert!(!rewrite.integer_work_exhausted);
    assert!(!rewrite.unsupported_integer_scope);

    let Term::Integer(IntegerTerm::Machine(machine)) = output else {
        panic!("the Integer machine observation changed carrier")
    };
    let Bitvector32Term::Variable(rewritten_load) = machine.value() else {
        panic!("the checked rewrite expanded a registered load into a memory tree")
    };
    assert_ne!(*rewritten_load, load);
    let (rewritten_memory, rewritten_pointer) =
        crate::kernel::eval::registered_load_for_variable(rewritten_load)
            .expect("the rewritten load must remain registered");
    assert_eq!(
        rewritten_memory, memory,
        "the proof snapshot must stay exact"
    );
    assert_eq!(
        rewritten_pointer.offset,
        PointerOffsetTerm::Constant(36),
        "the reminted pointer keeps the canonical byte offset for Integer 9"
    );
}
