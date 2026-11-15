use super::*;
use crate::kernel::VerificationSession;

fn word(memory: &SharedMemory, pointer: &Pointer, bytes: u32) -> MachineTerm {
    MachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
        memory,
        pointer,
        LoadKind::Bits64,
        bytes,
    ))
}
fn packed(value: &MachineTerm, parent: &Pointer) -> MachineTerm {
    MachineTerm::Binary {
        format: MachineIntegerType::UInt64,
        op: MachineBinaryOp::Add,
        left: Box::new(MachineTerm::PointerAddress(
            Box::new(parent.clone()),
            crate::kernel::AddressObjectClass::NONE,
        )),
        right: Box::new(MachineTerm::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::BitwiseAnd,
            left: Box::new(value.clone()),
            right: Box::new(MachineTerm::uint64_constant(1)),
        }),
    }
}
fn fact(a: MachineTerm, b: MachineTerm) -> Proposition {
    Proposition::ConditionIs(ConditionTerm::uint64_equal(a, b), true)
}
fn alias(a: &Pointer, b: &Pointer) -> Proposition {
    Proposition::ConditionIs(ConditionTerm::pointer_equal(a.clone(), b.clone()), true)
}
fn proved(context: &PureFactContext, goal: &Proposition) -> bool {
    crate::kernel::reasoning::required_obligation_is_exactly_discharged(context, goal)
}

fn raw_address(pointer: &Pointer) -> MachineTerm {
    // Deliberately bypass the surface constructor's address cancellation.
    MachineTerm::PointerAddress(Box::new(pointer.clone()), AddressObjectClass::NONE)
}

#[test]
fn integer_address_coordinates_join_word_classes_and_follow_scoped_equalities() {
    let _session = VerificationSession::enter();
    let bits = MachineTerm::Variable(Variable(960_001));
    let pointer = Pointer::symbolic(Variable(960_002));
    let decoded = Pointer::integer_address(bits.clone());
    let equation = fact(bits.clone(), raw_address(&pointer));
    let goal = Proposition::ConditionIs(
        ConditionTerm::uint64_equal(raw_address(&decoded), raw_address(&pointer)),
        true,
    );
    let base = PureFactContext::new();
    // Register the constructor before the premise, exercising a late merge.
    assert!(
        base.equality_graph
            .are_uint64_equal(&raw_address(&decoded), &bits)
    );
    assert!(!base.contains_known(&goal));
    let child = base.clone().assume_proposition(equation.clone());
    assert!(child.contains_known(&goal));
    assert!(
        child
            .equality_graph
            .are_uint64_equal(&raw_address(&decoded), &raw_address(&pointer))
    );
    assert!(!base.contains_known(&goal));
    assert!(!child.restricted_to_facts(&[], &[]).contains_known(&goal));
    let left = PointerValue::new(decoded.clone(), ProgramType::Int32Pointer);
    let right = PointerValue::new(pointer.clone(), ProgramType::Int32Pointer);
    // A cast that already carries the exact original domain can compare its
    // numeric coordinates. A bare address name cannot manufacture that domain.
    let original_domain = right.clone().with_address(decoded.clone());
    assert!(child.contains_known(&Proposition::ConditionIs(
        ConditionTerm::PointerValueEqual(
            Box::new(original_domain.clone()),
            Box::new(right.clone())
        ),
        true,
    )));
    assert!(child.contains_known(&Proposition::ConditionIs(
        ConditionTerm::pointer_value_equal(original_domain, right.clone()),
        true,
    )));
    assert!(!child.contains_known(&Proposition::ConditionIs(
        ConditionTerm::pointer_equal(decoded, pointer),
        true,
    )));
    assert!(!child.pointer_designations_match(&left, &right));
    assert!(!child.contains_known(&Proposition::ConditionIs(
        ConditionTerm::pointer_value_equal(left, right),
        true,
    )));
}

#[test]
fn integer_address_definition_preserves_byte_displacements_and_load_states() {
    let _session = VerificationSession::enter();
    let bits = MachineTerm::Variable(Variable(960_003));
    let decoded = Pointer::integer_address(bits.clone());
    let shifted = Pointer {
        block: decoded.block.clone(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let sum = MachineTerm::uint64_add(bits.clone(), MachineTerm::uint64_constant(8));
    let graph = EqualityGraph::default();
    assert!(graph.are_uint64_equal(&raw_address(&shifted), &sum));
    assert!(!graph.are_uint64_equal(&raw_address(&shifted), &bits));
    // Equal numeric addresses connect compatible reads, not state identity.
    let memory = intern_memory(Memory::new().with_block("coordinates", 32));
    let pointer = Pointer {
        block: "coordinates".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let after = intern_memory(memory.memory().clone().store(
        pointer.clone(),
        ProgramValue::UInt64(MachineTerm::uint64_constant(19)),
    ));
    let mut graph = graph;
    assert!(!graph.are_uint64_equal(&word(&memory, &decoded, 8), &word(&memory, &pointer, 8)));
    graph.add_uint64_equality(&bits, &raw_address(&pointer));
    assert!(graph.are_uint64_equal(&word(&memory, &decoded, 8), &word(&memory, &pointer, 8)));
    assert!(!graph.are_uint64_equal(&word(&memory, &decoded, 8), &word(&after, &pointer, 8)));
}

#[test]
fn equal_integer_address_words_do_not_merge_pointer_names_or_domains() {
    let _session = VerificationSession::enter();
    let a = MachineTerm::Variable(Variable(960_005));
    let b = MachineTerm::Variable(Variable(960_006));
    let p = Pointer::integer_address(a.clone());
    let q = Pointer::integer_address(b.clone());
    let mut context = PureFactContext::new();
    assert!(
        !context
            .equality_graph
            .are_uint64_equal(&raw_address(&p), &raw_address(&q))
    );
    context = context.assume_proposition(fact(a, b));
    assert!(
        context
            .equality_graph
            .are_uint64_equal(&raw_address(&p), &raw_address(&q))
    );
    assert!(!context.equality_graph.are_equal(&p, &q));
    let p = PointerValue::new(p, ProgramType::Int32Pointer);
    let q = PointerValue::new(q, ProgramType::Int32Pointer);
    assert!(!context.pointer_designations_match(&p, &q));
    assert!(!context.contains_known(&Proposition::ConditionIs(
        ConditionTerm::pointer_value_equal(p, q),
        true,
    )));
}

#[test]
fn wide_read_and_packed_word_congruence_compose_early_and_late() {
    let _session = VerificationSession::enter();
    let memory = intern_memory(Memory::new().with_block("wide", 128));
    let zid = Pointer::symbolic(Variable(910_001));
    let sid = Pointer::symbolic(Variable(910_002));
    let p = Pointer::loaded_value(&memory, &Pointer::symbolic(Variable(910_003)));
    let q = Pointer::loaded_value(&memory, &Pointer::symbolic(Variable(910_004)));
    let v = word(&memory, &zid, 8);
    let a = word(&memory, &p, 8);
    let premise = fact(v.clone(), packed(&v, &sid));
    let goal = fact(a.clone(), packed(&a, &q));
    for early in [false, true] {
        let mut context = PureFactContext::new().defer_non_exact_condition_reasoning();
        if early {
            context = context
                .assume_proposition(alias(&p, &zid))
                .assume_proposition(alias(&q, &sid));
            assert!(!proved(&context, &goal), "the premise is necessary");
        }
        context = context.assume_proposition(premise.clone());
        if !early {
            assert!(!proved(&context, &goal));
            context = context.assume_proposition(alias(&p, &zid));
            assert!(proved(&context, &fact(a.clone(), v.clone())));
            assert!(!proved(&context, &goal), "parent alias is necessary");
            context = context.assume_proposition(alias(&q, &sid));
        }
        assert!(proved(&context, &goal));
        assert!(!proved(&context.restricted_to_facts(&[], &[]), &goal));
        let impossible = context
            .clone()
            .assume_condition(ConditionTerm::pointer_equal(q.clone(), sid.clone()), false);
        assert!(impossible.is_inconsistent());
        assert!(proved(&impossible, &goal));
        // Cached closure results must not survive a weakened sibling context.
        assert!(proved(&context, &goal));
    }
}

#[test]
fn wide_reads_preserve_state_width_and_value_sort() {
    let _session = VerificationSession::enter();
    let before = intern_memory(Memory::new().with_block("wide", 128));
    let p = Pointer::symbolic(Variable(920_001));
    let q = Pointer::symbolic(Variable(920_002));
    let after = intern_memory(before.memory().clone().store(
        p.clone(),
        ProgramValue::UInt64(MachineTerm::uint64_constant(9)),
    ));
    let a = word(&before, &p, 8);
    let b = word(&before, &q, 8);
    let mut graph = EqualityGraph::default();
    let sibling = graph.clone();
    graph.add_equality(&p, &q);
    assert!(graph.are_uint64_equal(&a, &b));
    assert!(!sibling.are_uint64_equal(&a, &b));
    assert!(!graph.are_uint64_equal(&a, &word(&after, &q, 8)));
    let narrow = MachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
        &before,
        &q,
        LoadKind::Int32,
        4,
    ));
    assert!(!graph.are_uint64_equal(&a, &narrow));
    let x = MachineTerm::Variable(Variable(920_010));
    let y = MachineTerm::Variable(Variable(920_011));
    graph.add_int32_equality(&x, &y);
    assert!(!graph.are_uint64_equal(&x, &y));
    let mut wide_only = EqualityGraph::default();
    wide_only.add_uint64_equality(&x, &y);
    assert!(!wide_only.are_int32_equal(&x, &y));
    // Equality of applications never implies equality of their operands.
    let r = Pointer::symbolic(Variable(920_003));
    wide_only.add_uint64_equality(&packed(&x, &p), &packed(&x, &r));
    assert!(!wide_only.are_equal(&p, &r));
}

#[test]
fn wide_equality_inputs_reconstruct_in_derived_graphs() {
    let _session = VerificationSession::enter();
    let p = Pointer::symbolic(Variable(930_001));
    let q = Pointer::symbolic(Variable(930_002));
    let a = MachineTerm::Variable(Variable(930_003));
    let b = MachineTerm::Variable(Variable(930_004));
    let mut graph = EqualityGraph::default();
    let mut derived = graph.input_root();
    graph.add_uint64_equality(&a, &packed(&b, &p));
    graph.add_equality(&p, &q);
    assert!(derived.append_inputs_from(&graph));
    assert!(derived.are_uint64_equal(&a, &packed(&b, &q)));
    assert!(!graph.input_root().are_uint64_equal(&a, &packed(&b, &q)));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/uint64_tests.rs");
}

#[test]
fn a_read_through_an_alias_equals_the_value_stored_at_the_other_spelling() {
    let _session = VerificationSession::enter();
    let memory = intern_memory(Memory::new().with_block("cells", 32));
    let stored_at = Pointer {
        block: "cells".into(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let after = intern_memory(memory.memory().clone().store(
        stored_at.clone(),
        ProgramValue::UInt64(MachineTerm::uint64_constant(5)),
    ));
    let alias_of = Pointer::symbolic(Variable(960_101));
    let read = word(&after, &alias_of, 8);
    let five = MachineTerm::uint64_constant(5);
    let base = PureFactContext::new();
    assert!(!base.equality_graph.are_uint64_equal(&read, &five));
    // The read keeps its own term; the alias equates it with the cell.
    let aliased = base
        .clone()
        .assume_proposition(alias(&alias_of, &stored_at));
    assert!(aliased.equality_graph.are_uint64_equal(&read, &five));
    // Registered before the alias is known, the read still meets the cell.
    let mut graph = EqualityGraph::default();
    assert!(!graph.are_uint64_equal(&read, &five));
    graph.add_equality(&alias_of, &stored_at);
    assert!(graph.are_uint64_equal(&read, &five));
    // Another state's read is not this cell's value.
    assert!(
        !aliased
            .equality_graph
            .are_uint64_equal(&word(&memory, &alias_of, 8), &five)
    );
}

#[test]
fn shared_wide_endpoint_queries_preserve_exact_sources_and_scope() {
    use crate::kernel::{KernelTermExport, KernelTermImport, MachineOperandView as V};
    let _session = VerificationSession::enter();
    let ty = MachineIntegerType::UInt64;
    let a = MachineTerm::Variable(Variable(984001));
    let b = MachineTerm::Variable(Variable(984002));
    let source = MachineTerm::Variable(Variable(984003));
    let query = MachineTerm::uint64_add(a, b);
    let root = KernelTermImport::default()
        .machine_arithmetic(ty, &query)
        .unwrap();
    let address = MachineTerm::pointer_address(Pointer::symbolic(Variable(984004)));
    let parent = PureFactContext::new().assume_proposition(fact(source.clone(), address));
    let exports = KernelTermExport::machine_export_count();
    assert!(
        parent
            .equality_graph
            .wide_equation_endpoints_equal_to(V::Shared(&root))
            .is_empty()
    );
    let edge = fact(source.clone(), query.clone());
    let child = parent.clone().assume_proposition(edge.clone());
    let shared = child
        .equality_graph
        .wide_equation_endpoints_equal_to(V::Shared(&root));
    let native = child
        .equality_graph
        .wide_equation_endpoints_equal_to(V::Legacy(&query));
    assert_eq!(shared, native);
    assert!(shared.contains(&source));
    assert!(
        parent
            .equality_graph
            .wide_equation_endpoints_equal_to(V::Shared(&root))
            .is_empty()
    );
    assert_eq!(KernelTermExport::machine_export_count(), exports);
}

#[test]
fn machine_observation_cast_round_trip_is_congruent_inside_arithmetic() {
    use crate::kernel::{
        CompareRelation, IntegerTerm, MachineIntegerType, SharedMachineIntegerTerm,
    };
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let _session = crate::kernel::VerificationSession::enter();
        let leaf = MachineTerm::PureFunctionApplication {
            name: "opaque_round_trip_probe".into(),
            arguments: vec![MachineTerm::Variable(Variable(989801))],
        };
        let observed = SharedMachineIntegerTerm::intern(format, leaf.clone());
        let round_trip = MachineTerm::IntegerToMachine {
            value: IntegerTerm::Machine(observed).into(),
            destination: format,
        };
        let parent = |left: MachineTerm| MachineTerm::Binary {
            format,
            op: crate::kernel::MachineBinaryOp::Add,
            left: left.into(),
            right: MachineTerm::Variable(Variable(989802)).into(),
        };
        let goal = crate::kernel::ConditionTerm::machine_compare(
            format,
            CompareRelation::Equal,
            parent(round_trip),
            parent(leaf),
        );
        assert_eq!(
            crate::kernel::PureFactContext::new().decide(&goal),
            Some(true),
            "{format:?}"
        );
    }
}

#[test]
fn machine_observation_round_trip_keeps_equality_scope_and_format() {
    use crate::kernel::{CompareRelation, IntegerTerm, SharedMachineIntegerTerm};
    let _session = VerificationSession::enter();
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let x = MachineTerm::Variable(Variable(989811));
        let y = MachineTerm::Variable(Variable(989812));
        let converted = MachineTerm::IntegerToMachine {
            destination: format,
            value: IntegerTerm::Machine(SharedMachineIntegerTerm::intern(format, x.clone())).into(),
        };
        let goal =
            ConditionTerm::machine_compare(format, CompareRelation::Equal, converted, y.clone());
        let edge = Proposition::ConditionIs(
            ConditionTerm::machine_compare(format, CompareRelation::Equal, x, y),
            true,
        );
        let parent = PureFactContext::new();
        assert_eq!(parent.decide(&goal), None);
        let child = parent.clone().assume_proposition(edge.clone());
        assert_eq!(child.decide(&goal), Some(true));
        assert_eq!(parent.decide(&goal), None);
    }
    // Integer-to-machine conversion is range-checked, not a wrapping cast.
    // Equal widths alone cannot justify converting a negative signed value
    // into its unsigned bit pattern.
    let signed = SharedMachineIntegerTerm::intern(
        MachineIntegerType::Int32,
        MachineTerm::constant(u32::MAX),
    );
    let changed_sign = MachineTerm::IntegerToMachine {
        destination: MachineIntegerType::UInt32,
        value: IntegerTerm::Machine(signed).into(),
    };
    assert_ne!(
        PureFactContext::new().decide(&ConditionTerm::equal(
            changed_sign,
            MachineTerm::constant(u32::MAX)
        )),
        Some(true)
    );
    let wide = SharedMachineIntegerTerm::intern(
        MachineIntegerType::UInt64,
        MachineTerm::uint64_constant(1u64 << 32),
    );
    let narrowed = MachineTerm::IntegerToMachine {
        destination: MachineIntegerType::UInt32,
        value: IntegerTerm::Machine(wide).into(),
    };
    assert_ne!(
        PureFactContext::new().decide(&ConditionTerm::equal(narrowed, MachineTerm::constant(0))),
        Some(true)
    );
}

#[test]
fn machine_observation_round_trip_covers_each_declared_integer_format() {
    use crate::kernel::{IntegerTerm, SharedMachineIntegerTerm};
    for format in [
        MachineIntegerType::Int8,
        MachineIntegerType::UInt8,
        MachineIntegerType::Int16,
        MachineIntegerType::UInt16,
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
        MachineIntegerType::Int128,
        MachineIntegerType::UInt128,
    ] {
        let _session = VerificationSession::enter();
        let source =
            SharedMachineIntegerTerm::intern(format, MachineTerm::Variable(Variable(989841)));
        let original = IntegerTerm::Machine(source);
        let converted = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            format,
            MachineTerm::IntegerToMachine {
                destination: format,
                value: original.clone().into(),
            },
        ));
        assert!(
            EqualityGraph::default().are_integer_equal(&converted, &original),
            "{format:?}"
        );
    }
}

#[test]
fn machine_fold_endpoint_congruence_retains_shared_operands() {
    use crate::kernel::{
        IntegerRangeFoldIndex, IntegerTerm, KernelTermExport, SharedIntegerRangeEndpoint,
    };
    for unsigned in [false, true] {
        let _session = VerificationSession::enter();
        let x = MachineTerm::Variable(Variable(989921));
        let y = MachineTerm::Variable(Variable(989922));
        let format = if unsigned {
            MachineIntegerType::UInt64
        } else {
            MachineIntegerType::Int32
        };
        let fold = |value: MachineTerm| {
            let native = MachineTerm::Binary {
                format,
                op: MachineBinaryOp::Add,
                left: value.into(),
                right: if unsigned {
                    MachineTerm::uint64_constant(1)
                } else {
                    MachineTerm::constant(1)
                }
                .into(),
            };
            let root = crate::kernel::KernelTermImport::default()
                .machine_arithmetic(MachineIntegerType::Int32, &native)
                .unwrap();
            let endpoint = SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0))
                .with_shared_operand(root)
                .unwrap();
            assert!(!endpoint.machine_operand().has_boxed_operand());
            let index = if unsigned {
                IntegerRangeFoldIndex::UInt64 {
                    start: endpoint.clone(),
                    end: endpoint,
                }
            } else {
                IntegerRangeFoldIndex::Int32 {
                    start: endpoint.clone(),
                    end: endpoint,
                }
            };
            IntegerTerm::range_fold(
                index,
                IntegerTerm::constant_i64(0),
                Variable(989923),
                Variable(989924),
                IntegerTerm::var(Variable(989923)),
            )
        };
        let left = fold(x.clone());
        let right = fold(y.clone());
        let exports = KernelTermExport::machine_export_count();
        let mut graph = EqualityGraph::default();
        assert!(!graph.are_integer_equal(&left, &right));
        if unsigned {
            graph.add_uint64_equality(&x, &y);
        } else {
            graph.add_int32_equality(&x, &y);
        }
        assert!(graph.are_integer_equal(&left, &right));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
