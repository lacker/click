use super::*;
use crate::kernel::VerificationSession;
use crate::kernel::binary_node;

#[test]
fn complete_pointer_representative_exposes_a_stored_callback() {
    let _session = VerificationSession::enter();
    let ty = ProgramType::FunctionPointer(crate::kernel::CallbackSignature::UNSPECIFIED);
    let cell = Pointer::symbolic(Variable(998_965));
    let target = PointerValue::new(Pointer::function("callback"), ty);
    let memory = crate::kernel::intern_memory(
        Memory::new().store(cell.clone(), ProgramValue::Pointer(target.clone())),
    );
    let read = PointerValue::from_read(Pointer::loaded_value(&memory, &cell), ty, &memory, &cell);
    let graph = EqualityGraph::default();
    assert_eq!(graph.pointer_value_representative(&read), target);
    let unknown = PointerValue::from_read(
        Pointer::loaded_value(&memory, &cell.offset_by_bytes(8)),
        ty,
        &memory,
        &cell.offset_by_bytes(8),
    );
    assert_eq!(graph.pointer_value_representative(&unknown), unknown);
}

fn var(id: u64) -> MachineTerm {
    MachineTerm::Variable(Variable(id))
}
fn call(name: &str, arguments: Vec<PureFunctionArgument>) -> MachineTerm {
    MachineTerm::ClickFunctionApplication {
        name: name.into(),
        arguments,
    }
}
fn scalar(term: MachineTerm) -> PureFunctionArgument {
    PureFunctionArgument::Value(ProgramValue::Int32(term))
}
fn eq(a: MachineTerm, b: MachineTerm) -> Proposition {
    Proposition::ConditionIs(ConditionTerm::equal(a, b), true)
}
fn pointer(name: &str) -> Pointer {
    Pointer {
        block: name.into(),
        offset: PointerOffsetTerm::Constant(0),
    }
}
fn array(memory: &Memory, p: Pointer, element_type: ProgramType) -> PureFunctionArgument {
    PureFunctionArgument::ArrayRef {
        memory: memory.clone(),
        pointer: ProgramValue::Pointer(PointerValue::new(p, ProgramType::Int32Pointer)),
        element_type,
    }
}

#[test]
fn fact_lookup_uses_late_equalities_through_nested_applications() {
    let f = |x| call("f", vec![scalar(x)]);
    let g = |x| call("g", vec![scalar(f(x))]);
    let held = eq(g(var(1)), var(3));
    let required = eq(g(var(2)), var(4));
    let context = PureFactContext::new().assume_proposition(held);
    assert!(!context.contains_known(&required));
    let context = context
        .assume_proposition(eq(var(1), var(2)))
        .assume_proposition(eq(var(3), var(4)));
    assert!(context.contains_known(&required));
    assert!(!context.contains_assumed_exact(&required));
    assert!(!context.contains_known(&eq(call("other", vec![scalar(f(var(2)))]), var(4))));
    assert!(!context.contains_known(&eq(var(1), var(3)))); // no injectivity
}

#[test]
fn fact_lookup_transports_comparisons_and_negative_facts_without_arithmetic_search() {
    let held = Proposition::ConditionIs(ConditionTerm::signed_less_than(var(10), var(11)), false);
    let required =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(var(12), var(13)), false);
    let context = PureFactContext::new()
        .assume_proposition(held)
        .assume_proposition(eq(var(10), var(12)))
        .assume_proposition(eq(var(11), var(13)));
    assert!(context.contains_known(&required));
    assert!(!context.contains_known(&Proposition::ConditionIs(
        ConditionTerm::signed_less_than(var(12), var(13)),
        true
    )));
    assert!(!context.contains_known(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(var(12), var(13)),
        false
    )));
}

#[test]
fn fact_lookup_preserves_branch_restriction_and_contradiction() {
    let source = Proposition::ConditionIs(ConditionTerm::signed_less_than(var(20), var(21)), true);
    let target = Proposition::ConditionIs(ConditionTerm::signed_less_than(var(22), var(21)), true);
    let alias = eq(var(20), var(22));
    let parent = PureFactContext::new().assume_proposition(source.clone());
    let child = parent.clone().assume_proposition(alias.clone());
    assert!(child.contains_known(&target));
    assert!(!parent.contains_known(&target));
    assert!(
        !PureFactContext::new()
            .assume_proposition(alias)
            .contains_known(&target)
    );
    assert!(
        !child
            .restricted_to_facts(
                &[(ConditionTerm::signed_less_than(var(20), var(21)), true)],
                &[]
            )
            .contains_known(&target)
    );
    let replaced = child.assume_condition(ConditionTerm::signed_less_than(var(20), var(21)), false);
    assert!(replaced.is_inconsistent());
    assert!(replaced.contains_known(&source));
    assert!(replaced.contains_known(&target));
}

#[test]
fn pure_application_arguments_keep_states_types_and_argument_order() {
    let _session = VerificationSession::enter();
    let memory = Memory::new().with_block("p", 4).with_block("q", 4);
    let changed = memory
        .clone()
        .store(pointer("p"), ProgramValue::Int32(var(34)));
    let f = |memory: &Memory, p, ty| call("f", vec![array(memory, p, ty)]);
    let held = eq(f(&memory, pointer("p"), ProgramType::Int32), var(30));
    let context = PureFactContext::new()
        .assume_proposition(held)
        .assume_condition(
            ConditionTerm::PointerEqual(Box::new(pointer("p")), Box::new(pointer("q"))),
            true,
        );
    assert!(!context.contains_known(&eq(f(&memory, pointer("q"), ProgramType::Int32), var(30))));
    let context = context.assume_condition(
        ConditionTerm::PointerValueEqual(
            Box::new(PointerValue::new(pointer("p"), ProgramType::Int32Pointer)),
            Box::new(PointerValue::new(pointer("q"), ProgramType::Int32Pointer)),
        ),
        true,
    );
    assert!(context.contains_known(&eq(f(&memory, pointer("q"), ProgramType::Int32), var(30))));
    assert!(!context.contains_known(&eq(f(&changed, pointer("q"), ProgramType::Int32), var(30))));
    assert!(!context.contains_known(&eq(f(&memory, pointer("q"), ProgramType::UInt32), var(30))));
    let lhs = call("pair", vec![scalar(var(31)), scalar(var(32))]);
    let rhs = call("pair", vec![scalar(var(32)), scalar(var(31))]);
    assert!(!context.contains_known(&eq(lhs, rhs)));
}

#[test]
fn fact_congruence_keeps_predicate_truth_out_of_resource_equality_history() {
    let mut base = EqualityGraph::default();
    let condition = ConditionTerm::signed_less_than(var(40), var(41));
    base.add_condition(&condition, true);
    let mut derived = base.clone();
    let mut child = base.clone();
    child.add_int32_equality(&var(40), &var(42));
    let value_checkpoint = child.input_key();
    child.add_condition(&ConditionTerm::signed_less_than(var(42), var(43)), false);
    assert!(value_checkpoint == child.input_key());
    assert!(child.knows_condition(&ConditionTerm::signed_less_than(var(40), var(43)), false));
    assert!(derived.append_inputs_from(&child));
    assert!(!derived.knows_condition(&ConditionTerm::signed_less_than(var(40), var(43)), false));
    assert!(!base.knows_condition(&ConditionTerm::signed_less_than(var(40), var(43)), false));
    assert!(derived.knows_condition(&ConditionTerm::signed_less_than(var(42), var(41)), true));
    assert!(!base.knows_condition(&ConditionTerm::signed_less_than(var(42), var(41)), true));
}

#[test]
fn fact_lookup_uses_pointer_read_congruence_after_a_late_address_alias() {
    let _session = VerificationSession::enter();
    let memory = intern_memory(Memory::new());
    let a = Pointer::symbolic(Variable(72));
    let b = Pointer::symbolic(Variable(73));
    let f = |address: &Pointer| {
        call(
            "tag",
            vec![PureFunctionArgument::Value(ProgramValue::Pointer(
                PointerValue::new(
                    Pointer::loaded_value(&memory, address),
                    ProgramType::Int32Pointer,
                ),
            ))],
        )
    };
    let source = eq(f(&a), var(71));
    let target = eq(f(&b), var(71));
    let context = PureFactContext::new().assume_proposition(source.clone());
    assert!(!context.contains_known(&target));
    let alias = Proposition::ConditionIs(ConditionTerm::pointer_equal(a, b), true);
    let context = context.assume_proposition(alias.clone());
    assert!(context.contains_known(&target));
    assert!(
        !PureFactContext::new()
            .assume_proposition(alias)
            .contains_known(&target)
    );
}

#[test]
fn signed_addition_definedness_follows_early_and_late_operand_equalities() {
    let source = ConditionTerm::signed_add_overflows(var(60000), var(60001));
    let target = ConditionTerm::signed_add_overflows(var(60002), var(60003));
    let aliases = [eq(var(60000), var(60002)), eq(var(60001), var(60003))];
    for early in [false, true] {
        for truth in [false, true] {
            let mut facts = PureFactContext::new();
            if early {
                for alias in &aliases {
                    facts = facts.assume_proposition(alias.clone());
                }
            }
            facts = facts.assume_condition(source.clone(), truth);
            if !early {
                assert_eq!(facts.decide(&target), None);
                for alias in &aliases {
                    facts = facts.assume_proposition(alias.clone());
                }
            }
            assert_eq!(facts.decide(&target), Some(truth));
            assert_eq!(
                facts.decide(&ConditionTerm::signed_add_overflows(var(60003), var(60002))),
                Some(truth)
            );
            assert!(facts.contains_known(&Proposition::ConditionIs(target.clone(), truth)));
            assert!(!facts.contains_known(&Proposition::ConditionIs(target.clone(), !truth)));
            assert_eq!(
                facts.decide(&ConditionTerm::signed_subtract_overflows(
                    var(60002),
                    var(60003)
                )),
                None
            );
            assert_eq!(
                facts.decide(&ConditionTerm::int64_signed_add_overflows(
                    var(60002),
                    var(60003)
                )),
                None
            );
        }
    }
}

#[test]
fn signed_addition_definedness_stays_scoped() {
    let source = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(var(60100), var(60101)),
        false,
    );
    let target = ConditionTerm::signed_add_overflows(var(60102), var(60101));
    let alias = eq(var(60100), var(60102));
    let parent = PureFactContext::new().assume_proposition(source.clone());
    let child = parent.clone().assume_proposition(alias.clone());
    assert_eq!(child.decide(&target), Some(false));
    assert_eq!(parent.decide(&target), None);
    let alias_only = PureFactContext::new().assume_proposition(alias);
    assert_eq!(alias_only.decide(&target), None);
}

fn coordinate_pointer(block: PointerBlock, id: u64) -> Pointer {
    Pointer {
        block,
        offset: PointerOffsetTerm::Variable(Variable(id)),
    }
}

#[test]
fn pointer_disequality_projects_only_through_a_witnessed_common_base() {
    for alias_first in [false, true] {
        for block in [PointerBlock::ExternalArgument, "allocated".into()] {
            let source = Pointer::symbolic(Variable(70999));
            let left = coordinate_pointer(block.clone(), 71000);
            let right = coordinate_pointer(block, 71001);
            let alias = Proposition::ConditionIs(
                ConditionTerm::pointer_equal(source.clone(), left.clone()),
                true,
            );
            let distinct = Proposition::ConditionIs(
                ConditionTerm::pointer_equal(source.clone(), right.clone()),
                false,
            );
            let goal = Proposition::ConditionIs(
                ConditionTerm::pointer_offset_equal(left.offset.clone(), right.offset.clone()),
                false,
            );
            let parent = PureFactContext::new().assume_proposition(if alias_first {
                alias.clone()
            } else {
                distinct.clone()
            });
            assert!(!parent.contains_known(&goal));
            let child = parent.clone().assume_proposition(if alias_first {
                distinct.clone()
            } else {
                alias.clone()
            });
            assert!(child.contains_known(&goal));
            assert!(child.contains_known(&Proposition::ConditionIs(
                ConditionTerm::pointer_offset_equal(right.offset.clone(), left.offset.clone()),
                false
            )));
            assert!(!parent.contains_known(&goal));
        }
    }
    let distinct = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(pointer("allocation-a"), pointer("allocation-b")),
        false,
    );
    assert!(!distinct.contains_known(&Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(
            PointerOffsetTerm::Constant(0),
            PointerOffsetTerm::Constant(0)
        ),
        false
    )));
}

#[test]
fn pointer_disequality_follows_a_new_base_witness_on_the_kept_class() {
    let source = Pointer::symbolic(Variable(71999));
    let mut facts = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(source.clone(), coordinate_pointer("storage".into(), 72000)),
        false,
    );
    for i in 0..8 {
        facts = facts.assume_condition(
            ConditionTerm::pointer_equal(source.clone(), Pointer::symbolic(Variable(72100 + i))),
            true,
        );
    }
    facts = facts.assume_condition(
        ConditionTerm::pointer_equal(source, coordinate_pointer("storage".into(), 72001)),
        true,
    );
    assert!(facts.contains_known(&Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(
            PointerOffsetTerm::Variable(Variable(72000)),
            PointerOffsetTerm::Variable(Variable(72001))
        ),
        false
    )));
}

#[test]
fn pointer_disequality_projection_follows_offset_class_merges() {
    let source = Pointer::symbolic(Variable(76000));
    let left = coordinate_pointer(PointerBlock::ExternalArgument, 76001);
    let right = coordinate_pointer(PointerBlock::ExternalArgument, 76002);
    let replacement = coordinate_pointer(PointerBlock::ExternalArgument, 76003);
    let parent = PureFactContext::new()
        .assume_condition(
            ConditionTerm::pointer_equal(source.clone(), left.clone()),
            true,
        )
        .assume_condition(ConditionTerm::pointer_equal(source, right.clone()), false);
    let goal = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(replacement.offset.clone(), right.offset),
        false,
    );
    assert!(!parent.contains_known(&goal));
    let alias = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(left.offset, replacement.offset),
        true,
    );
    let child = parent.clone().assume_proposition(alias.clone());
    assert!(child.contains_known(&goal));
    assert!(!parent.contains_known(&goal));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/fact_congruence_tests.rs");
}

#[test]
fn pointer_comparison_preserves_base_evidence_through_aliases_and_scopes() {
    for alias_first in [false, true] {
        for query_first in [false, true] {
            let left = coordinate_pointer(PointerBlock::ExternalArgument, 77001);
            let right = coordinate_pointer(PointerBlock::ExternalArgument, 77002);
            let alias_pointer = Pointer::symbolic(Variable(77003));
            let source = Proposition::ConditionIs(
                ConditionTerm::pointer_equal(left.clone(), right.clone()),
                false,
            );
            assert!(matches!(
                &source,
                Proposition::ConditionIs(ConditionTerm::PointerEqual(..), false)
            ));
            let alias = Proposition::ConditionIs(
                ConditionTerm::pointer_equal(right.clone(), alias_pointer.clone()),
                true,
            );
            let goal = Proposition::ConditionIs(
                ConditionTerm::pointer_equal(left.clone(), alias_pointer.clone()),
                false,
            );
            let parent = PureFactContext::new().assume_proposition(if alias_first {
                alias.clone()
            } else {
                source.clone()
            });
            if query_first {
                assert!(!parent.contains_known(&goal));
            }
            let child = parent.clone().assume_proposition(if alias_first {
                source.clone()
            } else {
                alias.clone()
            });
            assert!(child.contains_known(&goal));
            assert!(child.contains_known(&Proposition::ConditionIs(
                ConditionTerm::pointer_equal(alias_pointer, left.clone()),
                false
            )));
            assert!(child.contains_known(&Proposition::ConditionIs(
                ConditionTerm::pointer_offset_equal(left.offset.clone(), right.offset.clone()),
                false
            )));
            assert!(!parent.contains_known(&goal));
            assert!(
                !PureFactContext::new()
                    .assume_proposition(alias)
                    .contains_known(&goal)
            );
            assert!(!child.contains_known(&Proposition::ConditionIs(
                ConditionTerm::pointer_equal(left, coordinate_pointer("other".into(), 77002)),
                false
            )));
        }
    }
}

// Reduced from the expanded zlib cursor join: two symbolic loop values meet
// a native C argument through signed prefix counts and a native length.
fn selected_cursor_chain() -> (Proposition, Vec<Proposition>) {
    let total = MachineTerm::Variable(Variable(2));
    let remaining = MachineTerm::Variable(Variable(1_000_002));
    let after = MachineTerm::Binary {
        format: MachineIntegerType::UInt64,
        op: MachineBinaryOp::Subtract,
        left: Box::new(remaining.clone()),
        right: Box::new(MachineTerm::uint64_constant(5552)),
    };
    let prefix = |remaining: MachineTerm| MachineTerm::ClickFunctionApplication {
        name: "prefix".into(),
        arguments: vec![
            PureFunctionArgument::Value(ProgramValue::UInt64(total.clone())),
            PureFunctionArgument::Value(ProgramValue::UInt64(remaining)),
        ],
    };
    let first = prefix(remaining);
    let count = prefix(after.clone());
    let sum = binary_node!(
        Int32,
        Add,
        Box::new(first.clone()),
        Box::new(MachineTerm::constant(5552)),
    );
    let difference = MachineTerm::Binary {
        format: MachineIntegerType::UInt64,
        op: MachineBinaryOp::Subtract,
        left: Box::new(total.clone()),
        right: Box::new(after),
    };
    let original = PointerValue::new(
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(100_001)), 1),
        },
        ProgramType::UInt8Pointer,
    );
    let batch = PointerValue::new(
        Pointer::symbolic(Variable(1_000_001)),
        ProgramType::UInt8Pointer,
    );
    let cursor_base = PointerValue::new(
        Pointer::symbolic(Variable(1_000_005)),
        ProgramType::UInt8Pointer,
    );
    let cursor = cursor_base
        .clone()
        .with_address(cursor_base.pointer().offset_by_bytes(16));
    let at_first = original.clone().with_address(Pointer {
        block: original.pointer().block.clone(),
        offset: PointerOffsetTerm::add(
            original.pointer().offset.clone(),
            PointerOffsetTerm::scale_int32(first.clone(), 1),
        ),
    });
    let at_sum = Pointer {
        block: original.pointer().block.clone(),
        offset: PointerOffsetTerm::add(
            original.pointer().offset.clone(),
            PointerOffsetTerm::scale_int32(sum.clone(), 1),
        ),
    };
    let at_count = Pointer {
        block: original.pointer().block.clone(),
        offset: PointerOffsetTerm::add(
            original.pointer().offset.clone(),
            PointerOffsetTerm::scale_int32(count.clone(), 1),
        ),
    };
    let target = original.clone().with_address(Pointer {
        block: original.pointer().block.clone(),
        offset: PointerOffsetTerm::add(
            original.pointer().offset.clone(),
            PointerOffsetTerm::scale_int64(difference, 1, true),
        ),
    });
    let full = |left: PointerValue, right: PointerValue| {
        Proposition::ConditionIs(
            ConditionTerm::PointerValueEqual(Box::new(left), Box::new(right)),
            true,
        )
    };
    let address = |left: Pointer, right: Pointer| {
        Proposition::ConditionIs(
            ConditionTerm::PointerEqual(Box::new(left), Box::new(right)),
            true,
        )
    };
    let premises = vec![
        full(
            cursor.clone(),
            batch
                .clone()
                .with_address(batch.pointer().offset_by_bytes(5552)),
        ),
        full(batch, at_first.clone()),
        address(at_first.pointer().offset_by_bytes(5552), at_sum),
        Proposition::ConditionIs(ConditionTerm::equal(count, sum), true),
        address(target.pointer().clone(), at_count),
    ];
    let goal = full(cursor, target);
    (goal, premises)
}

#[test]
fn full_pointer_queries_refresh_late_address_aliases() {
    use crate::kernel::proof::fact_reasoning::normalize_using_conditions;
    let (goal, premises) = selected_cursor_chain();
    let Proposition::ConditionIs(condition, value) = &goal else {
        unreachable!()
    };
    for indices in [[0, 1, 2, 3, 4], [2, 1, 4, 0, 3], [4, 3, 2, 1, 0]] {
        let ambient = indices.map(|index| premises[index].clone());
        let facts = crate::kernel::proof::ProofFacts::from_ordered(&ambient);
        assert!(
            facts
                .assumptions()
                .equality_graph
                .knows_condition(condition, *value),
            "admission order {indices:?}"
        );
        normalize_using_conditions(&goal, &premises, &facts).expect("selected cursor chain");
    }
}

#[test]
fn selected_cursor_chain_needs_its_support_and_displacement() {
    use crate::kernel::proof::{ProofFacts, fact_reasoning::normalize_using_conditions};
    let (goal, premises) = selected_cursor_chain();
    for missing in 0..premises.len() {
        let selected: Vec<_> = premises
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != missing)
            .map(|(_, p)| p.clone())
            .collect();
        let facts = ProofFacts::from_ordered(&selected);
        assert!(
            normalize_using_conditions(&goal, &selected, &facts).is_err(),
            "missing premise {missing}"
        );
    }
    let Proposition::ConditionIs(ConditionTerm::PointerValueEqual(left, right), true) = &goal
    else {
        unreachable!()
    };
    let wrong = Proposition::ConditionIs(
        ConditionTerm::PointerValueEqual(
            Box::new(
                (**left)
                    .clone()
                    .with_address(left.pointer().offset_by_bytes(1)),
            ),
            right.clone(),
        ),
        true,
    );
    let facts = ProofFacts::from_ordered(&premises);
    assert!(normalize_using_conditions(&wrong, &premises, &facts).is_err());
}

#[test]
fn refreshed_address_aliases_do_not_establish_pointer_identity() {
    use crate::kernel::proof::{ProofFacts, fact_reasoning::normalize_using_conditions};
    let (goal, mut premises) = selected_cursor_chain();
    let Proposition::ConditionIs(ConditionTerm::PointerValueEqual(left, right), true) =
        &premises[0]
    else {
        unreachable!()
    };
    premises[0] = Proposition::ConditionIs(
        ConditionTerm::pointer_equal(left.pointer().clone(), right.pointer().clone()),
        true,
    );
    let Proposition::ConditionIs(ConditionTerm::PointerValueEqual(left, right), true) = &goal
    else {
        unreachable!()
    };
    // Establish the numeric result independently of value identity.
    premises.push(Proposition::ConditionIs(
        ConditionTerm::pointer_equal(left.pointer().clone(), right.pointer().clone()),
        true,
    ));
    let facts = ProofFacts::from_ordered(&premises);
    assert!(
        facts
            .assumptions()
            .equality_graph
            .are_equal(left.pointer(), right.pointer())
    );
    assert!(normalize_using_conditions(&goal, &premises, &facts).is_err());
}

#[test]
fn selected_native_cursor_normalization_is_stable_across_context_orders() {
    use crate::kernel::proof::{ProofFacts, fact_reasoning::normalize_using_conditions};
    let original = PointerValue::new(
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(100_001)), 1),
        },
        ProgramType::UInt8Pointer,
    );
    let batch = PointerValue::new(
        Pointer::symbolic(Variable(1_000_001)),
        ProgramType::UInt8Pointer,
    );
    let root = PointerValue::new(
        Pointer::symbolic(Variable(1_000_005)),
        ProgramType::UInt8Pointer,
    );
    let cursor = root
        .clone()
        .with_address(root.pointer().offset_by_bytes(16));
    let first = MachineTerm::Variable(Variable(10));
    let second = MachineTerm::Variable(Variable(11));
    let at_first = original.clone().with_address(Pointer {
        block: original.pointer().block.clone(),
        offset: PointerOffsetTerm::add(
            original.pointer().offset.clone(),
            PointerOffsetTerm::scale_int64(first.clone(), 1, true),
        ),
    });
    let at_second = batch.clone().with_address(Pointer {
        block: batch.pointer().block.clone(),
        offset: PointerOffsetTerm::scale_int64(second.clone(), 1, true),
    });
    let sequential = Pointer {
        block: original.pointer().block.clone(),
        offset: PointerOffsetTerm::add(
            at_first.pointer().offset.clone(),
            PointerOffsetTerm::scale_int64(second.clone(), 1, true),
        ),
    };
    let target = original.clone().with_address(Pointer {
        block: original.pointer().block.clone(),
        offset: PointerOffsetTerm::add(
            original.pointer().offset.clone(),
            PointerOffsetTerm::scale_int64(
                MachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::Add,
                    left: Box::new(first),
                    right: Box::new(second),
                },
                1,
                true,
            ),
        ),
    });
    let full = |left: PointerValue, right: PointerValue| {
        Proposition::ConditionIs(
            ConditionTerm::PointerValueEqual(Box::new(left), Box::new(right)),
            true,
        )
    };
    let premises = [
        full(cursor.clone(), at_second),
        full(batch, at_first),
        Proposition::ConditionIs(
            ConditionTerm::pointer_equal(sequential, target.pointer().clone()),
            true,
        ),
    ];
    let goal = full(cursor, target);
    for order in [[2, 0, 1], [0, 1, 2], [1, 2, 0]] {
        let ambient = order.map(|index| premises[index].clone());
        let facts = ProofFacts::from_ordered(&ambient);
        for attempt in 0..32 {
            normalize_using_conditions(&goal, &premises, &facts).unwrap_or_else(|error| {
                panic!("ambient order {order:?}, attempt {attempt}: {error:?}")
            });
        }
    }
    for missing in 0..premises.len() {
        let selected: Vec<_> = premises
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != missing)
            .map(|(_, premise)| premise.clone())
            .collect();
        let facts = ProofFacts::from_ordered(&selected);
        assert!(
            normalize_using_conditions(&goal, &selected, &facts).is_err(),
            "missing premise {missing}"
        );
    }
}

#[test]
fn checked_pointer_read_retention_keeps_a_simplified_address_equation() {
    let _session = VerificationSession::enter();
    let memory = intern_memory(Memory::new());
    let address = Pointer::symbolic(Variable(9072));
    let read = Pointer::loaded_value(&memory, &address);
    let named = Pointer::symbolic(Variable(9073));
    let value =
        PointerValue::new(read.clone(), ProgramType::Int32Pointer).with_address(named.clone());
    let fact = crate::kernel::ExecutionPureFact::logical_read_equation(value, read.clone());
    assert!(matches!(
        fact.proposition(),
        Proposition::ConditionIs(ConditionTerm::PointerEqual(..), true)
    ));
    let context = PureFactContext::new();
    let isolated = context.clone();
    let untrusted = crate::kernel::ExecutionPureFact::new(fact.proposition().clone());
    untrusted.retain_pointer_read_definition(&context);
    assert!(!context.pointers_known_equal(&named, &read));
    fact.retain_pointer_read_definition(&context);
    assert!(context.pointers_known_equal(&named, &read));
    assert!(!context.designations_equal(&named, &read));
    assert!(!isolated.pointers_known_equal(&named, &read));
}

#[test]
fn named_pointer_read_definitions_follow_later_observations() {
    let _session = crate::kernel::VerificationSession::enter();
    let name = |memory: &SharedMemory, cell: &Pointer| {
        Pointer::loaded_value(
            &crate::kernel::memory_provenance::canonical_value_load_memory(memory, cell, 8),
            cell,
        )
    };
    let cell = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let unrelated = Pointer {
        block: PointerBlock::Heap(985_003),
        offset: PointerOffsetTerm::Constant(0),
    };
    let first = crate::kernel::intern_memory(
        Memory::new().store(unrelated.clone(), ProgramValue::UInt32(1u32.into())),
    );
    let named = name(&first, &cell);
    let context = PureFactContext::new();
    assert!(context.pointers_known_equal(&named, &Pointer::loaded_value(&first, &cell)));
    let later = crate::kernel::intern_memory(
        first
            .memory()
            .clone()
            .store(unrelated, ProgramValue::UInt32(2u32.into())),
    );
    let later_read = Pointer::loaded_value(&later, &cell);
    // Register both endpoints before their structural equation arrives.
    // Refresh must work even when neither query endpoint is a new graph term.
    let _ = context.equality_graph.address_class(&later_read);
    assert_eq!(named, name(&later, &cell));
    assert!(PureFactContext::new().pointers_known_equal(&named, &later_read));
    assert!(
        crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
            &named,
            &later_read,
            &context
        )
    );
    assert!(context.pointers_known_equal(&named, &later_read));
    assert!(
        PureFactContext::new().pointers_known_equal(&named, &Pointer::loaded_value(&first, &cell))
    );
}

#[test]
fn structural_pointer_read_definitions_keep_domains_and_reject_partial_writes() {
    let _session = VerificationSession::enter();
    let cell = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = intern_memory(Memory::new().store(
        Pointer {
            block: PointerBlock::Heap(986_005),
            offset: PointerOffsetTerm::Constant(0),
        },
        ProgramValue::UInt32(1u32.into()),
    ));
    let named_memory =
        crate::kernel::memory_provenance::canonical_value_load_memory(&memory, &cell, 8);
    let named = PointerValue::new(
        Pointer::loaded_value(&named_memory, &cell),
        ProgramType::Int32Pointer,
    );
    let original = PointerValue::new(
        Pointer::loaded_value(&memory, &cell),
        ProgramType::Int32Pointer,
    );
    let context = PureFactContext::new();
    assert!(context.equality_graph.knows_condition(
        &ConditionTerm::PointerValueEqual(Box::new(named.clone()), Box::new(original)),
        true,
    ));
    let changed = intern_memory(
        memory
            .memory()
            .clone()
            .store(cell.offset_by_bytes(4), ProgramValue::UInt32(9u32.into())),
    );
    let changed_memory =
        crate::kernel::memory_provenance::canonical_value_load_memory(&changed, &cell, 8);
    let changed = PointerValue::new(
        Pointer::loaded_value(&changed_memory, &cell),
        ProgramType::Int32Pointer,
    );
    assert!(!context.equality_graph.knows_condition(
        &ConditionTerm::PointerValueEqual(Box::new(named), Box::new(changed)),
        true,
    ));
}

#[test]
fn stored_pointer_read_definitions_preserve_bounds_and_reject_partial_overwrites() {
    let _session = VerificationSession::enter();
    let slot = Pointer::symbolic(Variable(987_001));
    let target = Pointer::symbolic(Variable(987_002));
    let stored = PointerValue::new(target.clone(), ProgramType::Int32Pointer).with_extent(Some(
        SubobjectExtent {
            start: target.clone(),
            width: 4u32.into(),
        },
    ));
    let memory =
        intern_memory(Memory::new().store(slot.clone(), ProgramValue::Pointer(stored.clone())));
    let read = PointerValue::new(
        Pointer::loaded_value(&memory, &slot),
        ProgramType::Int32Pointer,
    );
    assert_ne!(read, stored);
    let facts = PureFactContext::new();
    assert!(facts.equality_graph.knows_condition(
        &ConditionTerm::PointerValueEqual(Box::new(read.clone()), Box::new(stored.clone())),
        true
    ));
    let larger = stored.clone().with_extent(Some(SubobjectExtent {
        start: target,
        width: 8u32.into(),
    }));
    assert!(!facts.equality_graph.knows_condition(
        &ConditionTerm::PointerValueEqual(Box::new(read), Box::new(larger)),
        true
    ));
    let changed = intern_memory(
        memory
            .memory()
            .clone()
            .store(slot.offset_by_bytes(4), ProgramValue::UInt32(9u32.into())),
    );
    let changed_read = PointerValue::new(
        Pointer::loaded_value(&changed, &slot),
        ProgramType::Int32Pointer,
    );
    assert!(!facts.equality_graph.knows_condition(
        &ConditionTerm::PointerValueEqual(Box::new(changed_read), Box::new(stored)),
        true
    ));
}

#[test]
fn a_fact_retained_pointer_cache_is_not_an_unconditional_read_definition() {
    let _session = VerificationSession::enter();
    let slot = Pointer::symbolic(Variable(987_010));
    let other = Pointer::symbolic(Variable(987_011));
    let stored = PointerValue::new(
        Pointer::symbolic(Variable(987_012)),
        ProgramType::Int32Pointer,
    );
    let written = MemoryRange::new(other, 0u32.into(), 2u32.into());
    let separated = PureFactContext::new().assume_proposition(Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(written.clone())),
        right: Box::new(Resource::Memory(MemoryRange::new(
            slot.clone(),
            0u32.into(),
            2u32.into(),
        ))),
    });
    let before = Memory::new().store(slot.clone(), ProgramValue::Pointer(stored.clone()));
    let after = before.with_call_memory_havoc(Variable(987_013), &[written], &separated, None);
    assert_eq!(
        after.known_value(&slot),
        Some(ProgramValue::Pointer(stored.clone()))
    );
    let read = PointerValue::new(
        Pointer::loaded_value(&intern_memory(after), &slot),
        ProgramType::Int32Pointer,
    );
    assert!(!PureFactContext::new().equality_graph.knows_condition(
        &ConditionTerm::PointerValueEqual(Box::new(read), Box::new(stored)),
        true
    ));
}

#[test]
fn pointer_domain_queries_register_stored_read_definitions_without_prior_address_queries() {
    let _session = VerificationSession::enter();
    let slot = Pointer::symbolic(Variable(989_100));
    let target = Pointer::symbolic(Variable(989_101));
    let stored = PointerValue::new(target.clone(), ProgramType::Int32Pointer);
    let memory =
        intern_memory(Memory::new().store(slot.clone(), ProgramValue::Pointer(stored.clone())));
    let read = Pointer::loaded_value(&memory, &slot);
    let root = Pointer {
        block: PointerBlock::Heap(989_102),
        offset: PointerOffsetTerm::Constant(0),
    };
    let root_memory = intern_memory(Memory::new().store(
        slot.clone(),
        ProgramValue::typed_pointer(root, ProgramType::Int32Pointer),
    ));
    let root_read = Pointer::loaded_value(&root_memory, &slot);
    // Each query starts with a cold graph. A preceding numeric/full-pointer
    // equality query must not be needed to make its domain definition visible.
    assert_eq!(
        [
            EqualityGraph::default().designations_equal(&read, stored.designation()),
            EqualityGraph::default().opaque_extents_equal(&read, stored.opaque_extent().unwrap()),
            EqualityGraph::default().opaque_extent_is_root(&root_read),
        ],
        [true, true, true]
    );
    let partial = intern_memory(
        memory
            .memory()
            .clone()
            .store(slot.offset_by_bytes(4), ProgramValue::UInt32(0u32.into())),
    );
    let partial_read = Pointer::loaded_value(&partial, &slot);
    assert!(!EqualityGraph::default().designations_equal(&partial_read, stored.designation()));
    assert!(
        !EqualityGraph::default()
            .opaque_extents_equal(&partial_read, stored.opaque_extent().unwrap())
    );
    assert!(!EqualityGraph::default().opaque_extent_is_root(&partial_read));
}

#[test]
fn native_and_shared_word_arguments_have_the_same_typed_call_congruence() {
    let _session = VerificationSession::enter();
    let word = MachineTerm::add(var(998_730), MachineTerm::constant(3));
    let root = crate::kernel::KernelTermImport::default()
        .machine(crate::kernel::MachineIntegerType::Int32, &word);
    let shared = PureFunctionArgument::SharedMachine(
        crate::kernel::SharedMachineIntegerTerm::from_shared(
            crate::kernel::MachineIntegerType::Int32,
            root.clone(),
        )
        .unwrap(),
    );
    let native = scalar(word);
    assert_eq!(native.machine_identity(), shared.machine_identity());
    let native_application =
        crate::kernel::SharedPureApplication::intern("typed_call".into(), vec![native.clone()]);
    let shared_application =
        crate::kernel::SharedPureApplication::intern("typed_call".into(), vec![shared.clone()]);
    assert_eq!(native_application, shared_application);
    assert!(matches!(
        native_application.arguments()[0],
        PureFunctionArgument::Value(_)
    ));
    assert!(matches!(
        shared_application.arguments()[0],
        PureFunctionArgument::SharedMachine(_)
    ));
    let held = eq(call("typed_call", vec![native]), var(998_731));
    let context = PureFactContext::new().assume_proposition(held);
    let exports = crate::kernel::KernelTermExport::machine_export_count();
    assert!(context.contains_known(&eq(call("typed_call", vec![shared]), var(998_731))));
    let unsigned = PureFunctionArgument::SharedMachine(
        crate::kernel::SharedMachineIntegerTerm::from_shared(
            crate::kernel::MachineIntegerType::UInt32,
            root.with_machine_observation_type(crate::kernel::MachineIntegerType::UInt32),
        )
        .unwrap(),
    );
    assert!(!context.contains_known(&eq(call("typed_call", vec![unsigned]), var(998_731))));
    assert_eq!(
        crate::kernel::KernelTermExport::machine_export_count(),
        exports
    );
}
