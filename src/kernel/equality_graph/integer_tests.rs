use super::algebraic_tests::{model_type, variable};
use super::*;
use crate::kernel::{IntegerTerm as I, MachineIntegerType as M, SharedIntegerTerm};

fn cached(model: &AlgebraicTerm) -> I {
    I::from_machine(
        M::Int32,
        MachineTerm::ClickFunctionApplication {
            name: "cached".into(),
            arguments: vec![PureFunctionArgument::Algebraic(model.clone())],
        },
    )
    .unwrap()
}
fn count(model: &AlgebraicTerm) -> I {
    I::add(I::constant_i64(1), cached(model))
}
fn eq(a: I, b: I) -> Proposition {
    Proposition::ConditionIs(ConditionTerm::integer_equal(a, b), true)
}
fn alias(a: &AlgebraicTerm, b: &AlgebraicTerm) -> Proposition {
    Proposition::Equal(Term::Algebraic(a.clone()), Term::Algebraic(b.clone()))
}

#[test]
fn integer_count_facts_follow_early_and_late_model_aliases() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = model_type(
        "IntegerModel",
        AlgebraicValueType::Program(ProgramType::Int32),
    );
    let a = variable(&ty, 920_101);
    let b = variable(&ty, 920_102);
    let same = alias(&a, &b);
    let total = I::Variable(Variable(920_103));
    let premise = eq(total.clone(), count(&a));
    let goal = eq(total, count(&b));
    for early in [false, true] {
        let mut context = PureFactContext::new();
        if early {
            context = context.assume_proposition(same.clone());
            assert!(!context.contains_known(&goal));
        }
        context = context.assume_proposition(premise.clone());
        if !early {
            assert!(!context.contains_known(&goal));
            context = context.assume_proposition(same.clone());
        }
        assert!(context.contains_known(&goal));
    }
}

fn operations(x: &SharedIntegerTerm) -> Vec<I> {
    let two: SharedIntegerTerm = I::constant_i64(2).into();
    vec![
        I::Negate(x.clone()),
        I::Add(x.clone(), two.clone()),
        I::Subtract(x.clone(), two.clone()),
        I::Multiply(x.clone(), two.clone()),
        I::TruncatingQuotient(x.clone(), two.clone()),
        I::TruncatingRemainder(x.clone(), two),
    ]
}

#[test]
fn integer_value_aliases_reach_operations_calls_and_input_checkpoints() {
    let _session = crate::kernel::VerificationSession::enter();
    let x: SharedIntegerTerm = I::Variable(Variable(920_111)).into();
    let y: SharedIntegerTerm = I::Variable(Variable(920_112)).into();
    let mut graph = EqualityGraph::default();
    for (a, b) in operations(&x).iter().zip(operations(&y).iter()) {
        assert!(!graph.are_integer_equal(a, b));
    }
    let sibling = graph.clone();
    let mut checkpoint = graph.input_root();
    graph.add_condition(&ConditionTerm::IntegerEqual(x.clone(), y.clone()), true);
    assert!(checkpoint.append_inputs_from(&graph));
    let call = |value: I| {
        I::PureFunctionApplication(SharedPureApplication::intern(
            "integer_call".into(),
            vec![PureFunctionArgument::Integer(value.into())],
        ))
    };
    for (a, b) in operations(&x).into_iter().zip(operations(&y)) {
        assert!(graph.are_integer_equal(&a, &b));
        assert!(graph.are_integer_equal(&call(a.clone()), &call(b.clone())));
        assert!(checkpoint.are_integer_equal(&a, &b));
        assert!(!sibling.are_integer_equal(&a, &b));
    }
    assert!(!graph.are_integer_equal(&operations(&x)[0], &operations(&x)[1]));
}

#[test]
fn integer_order_truth_follows_aliases_without_merging_unrelated_true_facts() {
    let _session = crate::kernel::VerificationSession::enter();
    let x: SharedIntegerTerm = I::Variable(Variable(920_121)).into();
    let y: SharedIntegerTerm = I::Variable(Variable(920_122)).into();
    for make in [
        ConditionTerm::IntegerLessThan,
        ConditionTerm::IntegerLessEqual,
        ConditionTerm::IntegerGreaterThan,
        ConditionTerm::IntegerGreaterEqual,
        ConditionTerm::IntegerNotEqual,
    ] {
        for value in [true, false] {
            let mut graph = EqualityGraph::default();
            let goal = make(y.clone(), I::constant_i64(5).into());
            graph.add_condition(&make(x.clone(), I::constant_i64(5).into()), value);
            assert!(!graph.knows_condition(&goal, value));
            graph.add_integer_equality(&x, &y);
            assert!(graph.knows_condition(&goal, value));
            assert!(!graph.are_integer_equal(&I::constant_i64(5), &I::constant_i64(6)));
        }
    }
}

#[test]
fn integer_observations_keep_machine_types_and_read_states() {
    let _session = crate::kernel::VerificationSession::enter();
    let bits = MachineTerm::Variable(Variable(920_131));
    let signed = I::from_machine(M::Int32, bits.clone()).unwrap();
    let unsigned = I::from_machine(M::UInt32, bits).unwrap();
    let graph = EqualityGraph::default();
    assert!(!graph.are_integer_equal(&signed, &unsigned));
    let p = Pointer::symbolic(Variable(920_132));
    let before = intern_memory(
        Memory::new().store(p.clone(), ProgramValue::Int32(MachineTerm::constant(7))),
    );
    let after = intern_memory(
        before
            .memory()
            .clone()
            .store(p.clone(), ProgramValue::Int32(MachineTerm::constant(9))),
    );
    let read = |memory| {
        I::from_machine(
            M::Int32,
            MachineTerm::MemoryLoad(memory, Box::new(p.clone()), LoadKind::Int32),
        )
        .unwrap()
    };
    assert!(!graph.are_integer_equal(&read(before), &read(after)));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/integer_tests.rs");
}

#[test]
fn literal_integer_identities_join_classes_without_rewriting_terms() {
    let _session = crate::kernel::VerificationSession::enter();
    let x = I::var(Variable(929001));
    let y = I::var(Variable(929002));
    let zero: SharedIntegerTerm = I::constant_i64(0).into();
    let one: SharedIntegerTerm = I::constant_i64(1).into();
    let premise = eq(x.clone(), y.clone());
    let context = PureFactContext::new().assume_proposition(premise.clone());
    for operation in [
        I::Add(x.clone().into(), zero.clone()),
        I::Add(zero.clone(), x.clone().into()),
        I::Subtract(x.clone().into(), zero.clone()),
        I::Multiply(x.clone().into(), one.clone()),
        I::Multiply(one, x.clone().into()),
    ] {
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(operation.clone().into(), y.clone().into()),
            true,
        );
        assert!(context.contains_known(&goal));
        assert!(!PureFactContext::new().contains_known(&goal));
        assert_ne!(operation, x);
    }
    for operation in [
        I::Multiply(x.clone().into(), zero.clone()),
        I::Multiply(zero.clone(), x.into()),
    ] {
        assert!(context.contains_known(&Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(operation.into(), zero.clone()),
            true
        )));
    }
}

#[test]
fn fold_endpoint_congruence_keeps_the_bound_body_exact() {
    use crate::kernel::{IntegerRangeFoldIndex, MachineBinaryOp as Op};
    let _session = crate::kernel::VerificationSession::enter();
    let endpoint = MachineTerm::Variable(Variable(989_781));
    let predecessor = MachineTerm::logical_machine_binary(
        M::Int32,
        Op::Subtract,
        endpoint.clone(),
        MachineTerm::constant(1),
    );
    let restored = MachineTerm::logical_machine_binary(
        M::Int32,
        Op::Add,
        predecessor,
        MachineTerm::constant(1),
    );
    let body = I::Variable(Variable(989_782));
    let fold = |end: MachineTerm, body: I| I::RangeFold {
        index: IntegerRangeFoldIndex::Int32 {
            start: crate::kernel::SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0)),
            end: crate::kernel::SharedIntegerRangeEndpoint::intern(end),
        },
        initial: I::constant_i64(0).into(),
        accumulator: Variable(989_782),
        item: Variable(989_783),
        body: body.into(),
    };
    let graph = EqualityGraph::default();
    assert!(graph.are_int32_equal(&restored, &endpoint));
    assert!(graph.are_integer_equal(
        &fold(restored.clone(), body.clone()),
        &fold(endpoint.clone(), body.clone())
    ));
    assert!(!graph.are_integer_equal(&fold(restored, body), &fold(endpoint, I::constant_i64(1))));
}

#[test]
fn integer_residue_projection_matches_the_legacy_wrapped_consequences() {
    use crate::kernel::machine_integer::{
        Operation, modular::wrapped_equality_of_integer_equality,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let observe = |n| I::from_machine(M::Int32, MachineTerm::Variable(Variable(n))).unwrap();
    let (x, y, z) = (observe(982700), observe(982701), observe(982702));
    let mut expressions = vec![x.clone(), I::Negate(x.clone().into())];
    for op in Operation::ALL {
        for right in [I::constant_i64(0), I::constant_i64(1), y.clone()] {
            expressions.push(op.exact(x.clone(), right));
        }
    }
    expressions
        .push(Operation::Add.exact(x.clone(), Operation::Subtract.exact(y.clone(), x.clone())));
    expressions
        .push(Operation::Subtract.exact(Operation::Add.exact(x.clone(), y.clone()), x.clone()));
    for left in expressions {
        for right in [I::constant_i64(0), I::constant_i64(4294967296), z.clone()] {
            let condition = ConditionTerm::IntegerEqual(left.clone().into(), right.clone().into());
            let Some(wrapped) = wrapped_equality_of_integer_equality(&condition, true) else {
                continue;
            };
            let mut graph = EqualityGraph::default();
            graph.add_integer_equality(&left.clone().into(), &right.clone().into());
            assert!(
                graph.knows_condition(&wrapped, true),
                "missing {wrapped:?} from {condition:?}"
            );
            let parent = graph.clone();
            graph.add_int32_equality(
                &MachineTerm::Variable(Variable(982702)),
                &MachineTerm::constant(7),
            );
            assert!(parent.knows_condition(&wrapped, true));
        }
    }
}

#[test]
fn integer_residue_consequence_needs_its_source() {
    let _session = crate::kernel::VerificationSession::enter();
    let x = MachineTerm::Variable(Variable(982703));
    let y = MachineTerm::Variable(Variable(982704));
    let source = eq(
        I::Subtract(
            I::from_machine(M::Int32, x.clone()).unwrap().into(),
            I::from_machine(M::Int32, y.clone()).unwrap().into(),
        ),
        I::constant_i64(0),
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::equal(MachineTerm::subtract(x, y), MachineTerm::constant(0)),
        true,
    );
    let context = PureFactContext::new().assume_proposition(source.clone());
    assert!(context.contains_known(&goal));
    assert!(!context.restricted_to_facts(&[], &[]).contains_known(&goal));
}

#[test]
fn constant_residue_projection_preserves_the_operation_alias_route() {
    use crate::kernel::machine_integer::{
        comparison::native_comparison_through_integer_operations,
        modular::wrapped_equality_of_integer_equality,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let x = I::from_machine(M::Int32, MachineTerm::Variable(Variable(982709))).unwrap();
    let exact = I::Subtract(x.clone().into(), x.into());
    let condition = ConditionTerm::IntegerEqual(exact.into(), I::constant_i64(0).into());
    assert!(wrapped_equality_of_integer_equality(&condition, true).is_none());
    let (native, truth, bounds) = native_comparison_through_integer_operations(&condition, true)
        .expect("the old operation alias route");
    let mut context = PureFactContext::new();
    for bound in bounds {
        for premise in bound.stating_facts() {
            context = context.assume_proposition(premise);
        }
    }
    let context = context.assume_condition(condition, true);
    assert!(context.contains_known(&Proposition::ConditionIs(native, truth)));
}

#[test]
fn cited_mathematical_guards_share_native_and_retained_call_observations() {
    use crate::kernel::{KernelTerm, SharedMachineIntegerTerm};
    let _session = crate::kernel::VerificationSession::enter();
    let call = |shared, name: &str| MachineTerm::ClickFunctionApplication {
        name: name.into(),
        arguments: vec![if shared {
            PureFunctionArgument::SharedMachine(SharedMachineIntegerTerm::intern(
                M::UInt64,
                MachineTerm::uint64_constant(7),
            ))
        } else {
            PureFunctionArgument::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(7)))
        }],
    };
    let difference = |shared| MachineTerm::Binary {
        format: M::UInt64,
        op: crate::kernel::MachineBinaryOp::Subtract,
        left: Box::new(call(shared, "guard_padded_length")),
        right: Box::new(call(shared, "guard_decimal_length")),
    };
    // The second shape exercises the shared graph's opaque If atom, whose
    // exact producer differs only in the pure-call argument representation.
    for conditional in [false, true] {
        let endpoint = |shared| {
            if conditional {
                MachineTerm::If {
                    condition: Box::new(ConditionTerm::Variable(Variable(982798))),
                    then_term: Box::new(difference(shared)),
                    else_term: Box::new(MachineTerm::uint64_constant(2)),
                }
            } else {
                difference(shared)
            }
        };
        let native = I::from_machine(M::UInt64, endpoint(false)).unwrap();
        let retained = I::Machine(
            SharedMachineIntegerTerm::from_shared(
                M::UInt64,
                KernelTerm::retained_native_machine_operand(M::UInt64, &endpoint(true)),
            )
            .expect("shared arithmetic"),
        );
        let left = I::from_machine(M::UInt64, MachineTerm::Variable(Variable(982799))).unwrap();
        for truth in [false, true] {
            let premise =
                ConditionTerm::IntegerLessThan(left.clone().into(), native.clone().into());
            let query =
                ConditionTerm::IntegerLessThan(left.clone().into(), retained.clone().into());
            let mut graph = EqualityGraph::default();
            graph.add_condition(&premise, truth);
            assert!(graph.knows_condition(&query, truth));
            assert!(!graph.knows_condition(&query, !truth));
        }
    }
}

#[test]
fn narrow_call_bounds_preserve_retained_argument_observation_identity() {
    use crate::kernel::{KernelTerm, SharedMachineIntegerTerm};
    let _session = crate::kernel::VerificationSession::enter();
    let length = |name: &str| MachineTerm::ClickFunctionApplication {
        name: name.into(),
        arguments: vec![PureFunctionArgument::Value(ProgramValue::UInt64(
            MachineTerm::Variable(Variable(982811)),
        ))],
    };
    let subtract = |left, right| MachineTerm::Binary {
        format: M::UInt64,
        op: crate::kernel::MachineBinaryOp::Subtract,
        left: Box::new(left),
        right: Box::new(right),
    };
    let index = subtract(
        MachineTerm::Variable(Variable(982812)),
        subtract(length("padded_length"), length("decimal_length")),
    );
    let retained = SharedMachineIntegerTerm::from_shared(
        M::UInt64,
        KernelTerm::retained_native_machine_operand(M::UInt64, &index),
    )
    .expect("retained index");
    let observed = SharedMachineIntegerTerm::intern(M::UInt64, index);
    let bound = |index| {
        ConditionTerm::narrow_compare(
            M::UInt8,
            crate::kernel::CompareRelation::LessEqual,
            MachineTerm::Constant {
                format: M::UInt8,
                bits: 48,
            },
            MachineTerm::ClickFunctionApplication {
                name: "decimal_digit".into(),
                arguments: vec![PureFunctionArgument::SharedMachine(index)],
            },
        )
    };
    let premise = bound(observed);
    let query = bound(retained);
    let selected =
        PureFactContext::new().assume_proposition(Proposition::ConditionIs(premise.clone(), true));
    let widened = crate::kernel::machine_integer::comparison::narrow_fact_widening(&query)
        .expect("narrow comparison");
    assert_eq!(
        selected.decide(&query),
        Some(true),
        "native narrow authority"
    );
    assert_eq!(selected.decide(&widened), Some(true), "widened authority");
    let mut graph = EqualityGraph::default();
    graph.add_condition(&premise, true);
    assert!(
        graph.knows_condition(&widened, true),
        "widened graph authority"
    );
}
