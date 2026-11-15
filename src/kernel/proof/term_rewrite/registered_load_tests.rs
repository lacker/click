//! Regression coverage for registered-load capture and nested reminting.
//!
//! These tests deliberately use checked `TermRewrite` entry points; they do
//! not inspect the collector's private summaries directly.

use super::*;
use crate::kernel::binary_node;
use crate::kernel::{
    IntegerRangeFoldIndex, IntegerTerm, MachineIntegerType, Memory, Pointer, PointerBlock,
    PointerOffsetTerm, SharedIntegerRangeEndpoint, SharedIntegerTerm, SharedMachineIntegerTerm,
    SharedMemory, Term, Variable,
};
use std::collections::BTreeMap;

fn memory() -> SharedMemory {
    crate::kernel::intern_memory(Memory::new().with_block("registered-load-capture", 64))
}

#[test]
fn checked_index_substitution_reprojects_the_selected_scalar_read() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = crate::kernel::intern_memory(memory().memory().clone().store(
        Pointer {
            block: PointerBlock::Concrete("registered-load-capture".into()),
            offset: PointerOffsetTerm::Constant(0),
        },
        ProgramValue::Int32(MachineTerm::constant(7)),
    ));
    let from = MachineTerm::Variable(Variable(3_219_010));
    let to = MachineTerm::Variable(Variable(3_219_011));
    let address = |index: MachineTerm| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(index, 4),
    };
    let read = |index: MachineTerm| {
        let pointer = address(index);
        crate::kernel::eval::record_load_access_width(memory.memory(), &pointer, 4);
        crate::kernel::eval::canonical_term(&MachineTerm::MemoryLoad(
            memory.clone(),
            Box::new(pointer),
            LoadKind::Int32,
        ))
    };
    let original = read(from.clone());
    let MachineTerm::MemoryLoad(projected, pointer, _) = &original else {
        panic!("structural read");
    };
    assert_ne!(*projected, memory);
    assert_eq!(
        crate::kernel::prelude::canonical_load_projection_source(projected, pointer),
        Some(memory.clone())
    );
    let mut rewrite = TermRewrite::for_bits_checked(&from, &to);
    rewrite.enable_registered_load_resolution();
    let actual = rewrite.bits(&original);
    assert_eq!(rewrite.refusal(), None);
    let expected = read(to.clone());
    assert_eq!(actual, expected);
    let observed = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
        MachineIntegerType::Int32,
        original,
    ));
    assert_eq!(
        TermRewrite::for_bits_checked(&from, &to).integer(&observed),
        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            expected
        ))
    );
}

fn exact_load(memory: &SharedMemory, pointer: &Pointer) -> Variable {
    crate::kernel::eval::load_variable_for_exact_cell(
        memory,
        pointer,
        crate::kernel::LoadKind::Int32,
        4,
    )
}

fn int32_fold(accumulator: Variable, item: Variable, body: IntegerTerm) -> IntegerTerm {
    IntegerTerm::range_fold(
        IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0)),
            end: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(1)),
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
        MachineTerm::Variable(variable),
    ))
}

#[test]
fn checked_program_substitution_reserves_free_integer_in_registered_load_pointer() {
    let memory = memory();
    let source = Variable(3_210_000);
    let free_integer = Variable(3_210_001);
    let accumulator = Variable(3_210_002);
    let inner_load = exact_load(
        &memory,
        &Pointer {
            block: PointerBlock::Concrete("registered-load-capture".into()),
            offset: PointerOffsetTerm::scaled_int32_node(
                MachineTerm::IntegerToMachine {
                    value: SharedIntegerTerm::from(IntegerTerm::Variable(free_integer)),
                    destination: MachineIntegerType::Int32,
                },
                4,
            ),
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
    let source_term = MachineTerm::Variable(source);
    let replacement_term = binary_node!(
        Int32,
        Add,
        Box::new(MachineTerm::Variable(load)),
        Box::new(MachineTerm::constant(1)),
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
    assert_eq!(
        body.as_ref(),
        &IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            replacement_term.clone(),
        ))
    );
    let (_, pointer) = crate::kernel::eval::registered_load_for_variable(&inner_load)
        .expect("replacement load must retain its defining pointer");
    assert!(matches!(pointer.offset,
        PointerOffsetTerm::Int32Scaled { value, .. }
            if matches!(value.structural_value(), MachineTerm::IntegerToMachine { value, .. }
                if matches!(value.as_ref(), IntegerTerm::Variable(variable)
                    if *variable == free_integer))));
}

#[test]
fn checked_program_substitution_reserves_free_program_in_registered_load_pointer() {
    let memory = memory();
    let source = Variable(3_220_000);
    let free_c = Variable(3_220_001);
    let accumulator = Variable(3_220_002);
    let load = exact_load(
        &memory,
        &Pointer {
            block: PointerBlock::Concrete("registered-load-capture".into()),
            offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(free_c), 4),
        },
    );
    let fold = int32_fold(accumulator, free_c, machine_variable(source));
    let source_term = MachineTerm::Variable(source);
    let replacement_term = MachineTerm::Variable(load);
    let mut rewrite = TermRewrite::for_bits_checked(&source_term, &replacement_term);
    rewrite.enable_registered_load_resolution();
    let output = rewrite.term(&Term::Integer(fold));
    assert!(!rewrite.integer_work_exhausted);
    assert!(!rewrite.unsupported_integer_scope);

    let Term::Integer(IntegerTerm::RangeFold { item, body, .. }) = output else {
        panic!("checked substitution dropped the C fold")
    };
    assert_ne!(item, free_c, "free C pointer input was captured");
    assert_eq!(body.as_ref(), &machine_variable(load));
    let (_, pointer) = crate::kernel::eval::registered_load_for_variable(&load)
        .expect("replacement load must retain its defining pointer");
    assert!(matches!(pointer.offset,
        PointerOffsetTerm::Int32Scaled { value, .. }
            if matches!(value.structural_value(), MachineTerm::Variable(variable)
                if *variable == free_c)));
}

#[test]
fn checked_registered_load_rewrite_remints_nested_direct_offset() {
    let memory = memory();
    let source = Variable(3_230_000);
    let inner_pointer = Pointer {
        block: PointerBlock::Concrete("registered-load-capture".into()),
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(source), 4),
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
    let source_term = MachineTerm::Variable(source);
    let replacement_term = MachineTerm::constant(9);
    let mut rewrite = TermRewrite::for_bits_checked(&source_term, &replacement_term);
    rewrite.enable_registered_load_resolution();
    let output = rewrite.term(&input);
    assert!(!rewrite.integer_work_exhausted);
    assert!(!rewrite.unsupported_integer_scope);

    let Term::Integer(IntegerTerm::Machine(machine)) = output else {
        panic!("nested registered load changed the Integer carrier")
    };
    assert!(!machine.has_boxed_operand());
    let (outer_memory, outer_pointer, kind) =
        machine.operand_view().read().expect("structural read");
    assert_eq!(kind, crate::kernel::LoadKind::Int32);
    assert_ne!(
        outer_pointer,
        &crate::kernel::eval::registered_load_for_variable(&outer)
            .unwrap()
            .1
    );
    assert_eq!(outer_memory, &memory);
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
fn checked_integer_binding_rewrites_registered_load_at_exact_state() {
    let memory = memory();
    let source = Variable(3_240_000);
    let pointer = Pointer {
        block: PointerBlock::Concrete("registered-load-capture".into()),
        offset: PointerOffsetTerm::scaled_int32_node(
            MachineTerm::IntegerToMachine {
                value: SharedIntegerTerm::from(IntegerTerm::var(source)),
                destination: MachineIntegerType::Int32,
            },
            4,
        ),
    };
    let load = exact_load(&memory, &pointer);
    let input = Term::Integer(machine_variable(load));
    let program_replacements = BTreeMap::new();
    let integer_replacements = BTreeMap::from([(source, IntegerTerm::constant_i64(9))]);
    let algebraic_replacements = BTreeMap::new();
    let mut rewrite = TermRewrite::for_checked_typed_variables(
        &program_replacements,
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
    let (rewritten_memory, rewritten_pointer, kind) =
        machine.operand_view().read().expect("structural read");
    assert_eq!(kind, crate::kernel::LoadKind::Int32);
    assert_eq!(rewritten_memory, &memory, "the proof state must stay exact");
    assert_eq!(
        rewritten_pointer.offset,
        PointerOffsetTerm::Constant(36),
        "the reminted pointer keeps the canonical byte offset for Integer 9"
    );
}

#[test]
fn shared_carrier_cache_preserves_current_registered_load_dependencies() {
    let _session = VerificationSession::enter();
    let address_variable = Variable(982802);
    let pointer = Pointer::symbolic(address_variable);
    let load = exact_load(&memory(), &pointer);
    let format = MachineIntegerType::Int32;
    let root = KernelTerm::machine_binary_shared(
        format,
        MachineBinaryOp::Add,
        [
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), load),
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), load),
        ],
    );
    let machine = SharedMachineIntegerTerm::from_shared(format, root).unwrap();
    let proposition = Proposition::ConditionIs(
        ConditionTerm::IntegerEqual(
            IntegerTerm::Machine(machine.clone()).into(),
            IntegerTerm::constant_i64(0).into(),
        ),
        true,
    );
    let collect = || {
        let mut collector = IntegerSubstitutionVariableCollector::checked();
        collector.collect(&proposition);
        assert!(!collector.exhausted());
        let mut found = BTreeSet::new();
        collector.extend_into(&mut found);
        found
    };
    assert_eq!(collect(), BTreeSet::from([load, address_variable]));
    assert_eq!(collect(), BTreeSet::from([load, address_variable]));
    assert!(!machine.has_boxed_operand());
    // A warm syntax cache must not retain a previous registry's dependencies.
    crate::kernel::eval::clear_load_variable_registry();
    assert_eq!(collect(), BTreeSet::from([load]));
    assert!(!machine.has_boxed_operand());
}

#[test]
fn named_read_replacement_reaches_a_shared_integer_observation() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let address = Pointer::symbolic(Variable(3_219_000));
    let source = MachineTerm::Variable(exact_load(&memory, &address));
    let replacement = MachineTerm::constant(7);
    let observed = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
        MachineIntegerType::Int32,
        source.clone(),
    ));
    let IntegerTerm::Machine(machine) = &observed else {
        unreachable!()
    };
    assert!(machine.shared_operand().unwrap().has_machine_reads());
    let mut rewrite = TermRewrite::for_bits_checked(&source, &replacement);
    let result = rewrite.integer(&observed);
    assert_eq!(rewrite.refusal(), None);
    assert!(rewrite.changed);
    assert_eq!(result, IntegerTerm::constant_i64(7));
}

#[test]
fn structural_read_replacement_matches_retained_name_at_native_value_boundary() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let address = Pointer::symbolic(Variable(3_219_001));
    let name = exact_load(&memory, &address);
    let named = MachineTerm::Variable(name);
    let read = MachineTerm::MemoryLoad(memory.clone(), Box::new(address.clone()), LoadKind::Int32);
    let observed = machine_variable(name);
    let replacement = MachineTerm::IntegerToMachine {
        value: SharedIntegerTerm::from(IntegerTerm::Add(
            machine_variable(exact_load(&memory, &address.offset_by_bytes(4))).into(),
            IntegerTerm::constant_i64(1).into(),
        )),
        destination: MachineIntegerType::Int32,
    };
    assert!(
        KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::Int32, &replacement)
            .is_none()
    );
    let mut expected = TermRewrite::for_bits_checked(&named, &replacement);
    let expected = expected.integer(&observed);
    assert_ne!(expected, observed);
    let mut rewrite = TermRewrite::for_bits_checked(&read, &replacement);
    let result = rewrite.integer(&observed);
    assert_eq!(rewrite.refusal(), None);
    assert_eq!(result, expected);
    let other = MachineTerm::MemoryLoad(
        memory,
        Box::new(address.offset_by_bytes(8)),
        LoadKind::Int32,
    );
    let mut rewrite = TermRewrite::for_bits_checked(&other, &replacement);
    assert_eq!(rewrite.integer(&observed), observed);
}

#[test]
fn resource_comparison_forms_reach_structural_scalar_read_arguments() {
    let _session = crate::kernel::VerificationSession::enter();
    let address = Pointer::symbolic(Variable(3_219_020));
    let memory = crate::kernel::intern_memory(
        Memory::new().store(address.clone(), ProgramValue::Int32(37u32.into())),
    );
    let relation = |term: MachineTerm| {
        let parent = Resource::Composite {
            name: "storage".into(),
            arguments: vec![AlgebraicValue::Integer(
                IntegerTerm::from_machine(MachineIntegerType::Int32, term.clone()).unwrap(),
            )]
            .into(),
        };
        let child = Resource::Composite {
            name: "allocation".into(),
            arguments: vec![AlgebraicValue::Program(ProgramValue::Int32(term))].into(),
        };
        Proposition::ResourceContains {
            parent: Box::new(parent),
            child: Box::new(child),
        }
    };
    let read =
        |memory, pointer| MachineTerm::MemoryLoad(memory, Box::new(pointer), LoadKind::Int32);
    let goal = relation(read(memory.clone(), address.clone()));
    let expected = relation(MachineTerm::constant(37));
    assert_eq!(
        crate::kernel::eval::comparison_form(&goal),
        Some(expected.clone())
    );
    assert!(crate::kernel::eval::proposition_mentions_scalar_read(&goal));
    let other_address = relation(read(memory, address.offset_by_bytes(4)));
    assert_ne!(
        crate::kernel::eval::comparison_form(&other_address),
        Some(expected.clone())
    );
    let other_memory = crate::kernel::intern_memory(
        Memory::new().store(address.clone(), ProgramValue::Int32(38u32.into())),
    );
    assert_ne!(
        crate::kernel::eval::comparison_form(&relation(read(other_memory, address))),
        Some(expected)
    );
}
