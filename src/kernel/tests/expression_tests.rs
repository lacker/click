// These tests exercise discovery explicitly through kernel::search::ProofSearch.
use super::*;
use crate::kernel::MachineCastSpelling;
use crate::kernel::binary_node;
use crate::kernel::{constant_u32, int32_constant};

#[test]
fn specification_pointer_values_do_not_adopt_fact_supplied_bounds() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer::symbolic(Variable(989_900));
    let value = PointerValue::new(pointer.clone(), ProgramType::Int32Pointer);
    let bounded = value.clone().with_extent(Some(SubobjectExtent {
        start: pointer,
        width: 4u32.into(),
    }));
    let empty = PureFactContext::new();
    let facts = empty.assume_condition(
        ConditionTerm::PointerValueEqual(Box::new(value.clone()), Box::new(bounded)),
        true,
    );
    assert_ne!(facts.pointer_value_at_entry(&value), value);
    let state = ExecutionState::new().with_local("p", ProgramValue::Pointer(value.clone()));
    let _specification = crate::kernel::eval::SpecificationReadScope::enter();
    for expression in [
        ProgramExpression::Value(ProgramValue::Pointer(value.clone())),
        ProgramExpression::Variable("p".to_owned()),
    ] {
        for context in [&PureFactContext::new(), &facts] {
            let paths = evaluate_program_expression_paths(
                &state,
                &expression,
                context,
                &mut ExecutionBudget::default(),
            )
            .unwrap();
            assert_eq!(paths.len(), 1);
            assert_eq!(
                paths[0].outcome,
                ExpressionOutcome::Value(ProgramValue::Pointer(value.clone())),
                "{expression:?}",
            );
        }
    }
}

/// The only specification-conditional branch lowering decides is the one a
/// literally constant condition folds away. Folding stays exact in both
/// directions; a condition that needs an ambient fact is not decided here,
/// so both branches are lowered and a proof step picks the arm.
#[test]
fn a_specification_condition_folds_only_when_it_is_constant() {
    let flag = MachineTerm::Variable(Variable(4241));
    let constant_true =
        ConditionTerm::signed_less_than(MachineTerm::constant(1), MachineTerm::constant(2));
    let constant_false =
        ConditionTerm::signed_less_than(MachineTerm::constant(2), MachineTerm::constant(1));
    let ambient = ConditionTerm::signed_less_than(MachineTerm::constant(0), flag.clone());

    for (condition, expected) in [(constant_true, true), (constant_false, false)] {
        assert_eq!(
            constant_spec_condition_value(&Proposition::ConditionIs(condition.clone(), true)),
            Some(expected)
        );
        assert_eq!(
            constant_spec_condition_value(&Proposition::ConditionIs(condition, false)),
            Some(!expected)
        );
    }

    // Ambient facts are exactly what lowering must not consult: the same
    // condition stays undecided however much the surrounding context knows.
    let knows_the_condition = PureFactContext::new().assume_condition(ambient.clone(), true);
    assert_eq!(knows_the_condition.decide(&ambient), Some(true));
    for value in [true, false] {
        assert_eq!(
            constant_spec_condition_value(&Proposition::ConditionIs(ambient.clone(), value)),
            None
        );
    }
}

// A specification's conversion owes each bound the context does not
// prove; C's conversion owes none and is the same low word.
#[test]
fn checked_wide_to_int_narrowing_requires_each_representability_bound() {
    let value = MachineTerm::Variable(Variable(912));
    let lower = ConditionTerm::int64_signed_greater_equal(
        value.clone(),
        MachineTerm::int64_constant(i64::from(i32::MIN)),
    );
    let signed_upper = ConditionTerm::int64_signed_less_equal(
        value.clone(),
        MachineTerm::int64_constant(i64::from(i32::MAX)),
    );
    let unsigned_upper = ConditionTerm::uint64_less_equal(
        value.clone(),
        MachineTerm::uint64_constant(i32::MAX as u64),
    );
    for (input, bounds) in [
        (
            ProgramValue::Int64(value.clone()),
            vec![lower, signed_upper],
        ),
        (ProgramValue::UInt64(value.clone()), vec![unsigned_upper]),
    ] {
        for provided in 0..=bounds.len() {
            let mut assumptions = PureFactContext::new();
            for bound in &bounds[..provided] {
                assumptions = assumptions.assume_condition(bound.clone(), true);
            }
            let mut obligations = Vec::new();
            let modular = crate::kernel::eval::coerce_program_value_to_type(
                input.clone(),
                ProgramType::Int32,
                &mut obligations,
                &assumptions,
            )
            .unwrap();
            assert_eq!(
                modular,
                ProgramValue::Int32(MachineTerm::uint32_from_64(value.clone()))
            );
            assert!(obligations.is_empty());
            let result = crate::kernel::eval::coerce_program_value_to_type_as(
                input.clone(),
                ProgramType::Int32,
                crate::kernel::eval::IntegerConversion::Checked,
                &mut obligations,
                &assumptions,
            )
            .unwrap();
            assert_eq!(result, modular);
            assert_eq!(obligations.len(), bounds.len() - provided);
            for (obligation, bound) in obligations.iter().zip(&bounds[provided..]) {
                assert_eq!(
                    obligation.proposition(),
                    &Proposition::ConditionIs(bound.clone(), true)
                );
            }
        }
    }
}

#[test]
fn wide_to_int_narrowing_checks_signed_and_unsigned_boundaries() {
    use crate::kernel::eval::IntegerConversion;
    let convert = |value: ProgramValue, conversion, obligations: &mut Vec<ProofObligation>| {
        crate::kernel::eval::coerce_program_value_to_type_as(
            value,
            ProgramType::Int32,
            conversion,
            obligations,
            &PureFactContext::new(),
        )
    };
    for value in [
        i64::MIN,
        i64::from(i32::MIN) - 1,
        i64::from(i32::MIN),
        -1,
        0,
        i64::from(i32::MAX),
        i64::from(i32::MAX) + 1,
        i64::MAX,
    ] {
        let mut obligations = Vec::new();
        let input = ProgramValue::Int64(MachineTerm::int64_constant(value));
        // C's conversion keeps the low word, read as signed.
        assert_eq!(
            convert(input.clone(), IntegerConversion::Modular, &mut obligations),
            Some(int32(value as u32))
        );
        assert!(obligations.is_empty());
        let result = convert(input, IntegerConversion::Checked, &mut obligations);
        assert_eq!(result, Some(int32(value as u32)));
        assert_eq!(obligations.is_empty(), i32::try_from(value).is_ok());
        for obligation in &obligations {
            let Proposition::ConditionIs(condition, true) = obligation.proposition() else {
                panic!("narrowing owes an explicit range comparison");
            };
            assert_eq!(
                PureFactContext::decide_intrinsically(condition),
                Some(false)
            );
            assert!(obligation.context().unwrap().starts_with("int32 narrowing"));
        }
    }
    for value in [
        0,
        i32::MAX as u64,
        i32::MAX as u64 + 1,
        u32::MAX as u64,
        u64::MAX,
    ] {
        let mut obligations = Vec::new();
        let input = ProgramValue::UInt64(MachineTerm::uint64_constant(value));
        assert_eq!(
            convert(input.clone(), IntegerConversion::Modular, &mut obligations),
            Some(int32(value as u32))
        );
        assert!(obligations.is_empty());
        let result = convert(input, IntegerConversion::Checked, &mut obligations);
        assert_eq!(result, Some(int32(value as u32)));
        assert_eq!(obligations.is_empty(), value <= i32::MAX as u64);
        for obligation in &obligations {
            let Proposition::ConditionIs(condition, true) = obligation.proposition() else {
                panic!("narrowing owes an explicit range comparison");
            };
            assert_eq!(
                PureFactContext::decide_intrinsically(condition),
                Some(false)
            );
            assert_eq!(obligation.context(), Some("int32 narrowing upper bound"));
        }
    }
}

#[test]
fn wide_equality_bounds_keep_width_sign_and_exact_premises() {
    let x = MachineTerm::Variable(Variable(950));
    let y = MachineTerm::Variable(Variable(951));
    let signed_bound =
        ConditionTerm::int64_signed_less_equal(x.clone(), MachineTerm::int64_constant(0));
    let unsigned_bound =
        ConditionTerm::uint64_less_equal(x.clone(), MachineTerm::uint64_constant(0));
    let facts = PureFactContext::new()
        .assume_condition(ConditionTerm::uint64_equal(x.clone(), y.clone()), true)
        .assume_condition(
            ConditionTerm::uint64_equal(y, MachineTerm::uint64_constant(u64::MAX)),
            true,
        );
    assert_eq!(facts.decide(&signed_bound), Some(true));
    assert_eq!(facts.decide(&unsigned_bound), Some(false));
    let narrowed = Proposition::ConditionIs(
        ConditionTerm::equal(
            MachineTerm::uint32_from_64(x.clone()),
            MachineTerm::constant(u32::MAX),
        ),
        true,
    );
    assert!(crate::kernel::search::ProofSearch::proves(
        &(facts),
        &narrowed
    ));
    assert!(
        crate::kernel::search::ProofSearch::derive_atomic_proposition(&(facts), &narrowed)
            .is_some()
    );
    assert!(
        crate::kernel::search::ProofSearch::derive_solve_atomic_proposition(&(facts), &narrowed)
            .is_some()
    );
    // A 32-bit equality is not evidence about all 64 bits of a wide term.
    let narrow_facts = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(x, MachineTerm::constant(0)), true);
    assert_eq!(narrow_facts.decide(&unsigned_bound), None);
    let proposition = Proposition::ConditionIs(signed_bound, true);
    let derivation =
        crate::kernel::search::ProofSearch::derive_atomic_proposition(&(facts), &proposition)
            .unwrap();
    assert!(derivation.check(&facts));
    assert!(!derivation.check(&PureFactContext::new()));
}

#[test]
fn unsigned_64_to_32_narrowing_preserves_only_low_bits() {
    for (input, expected) in [
        (MachineTerm::uint64_constant(u64::MAX), u32::MAX),
        (MachineTerm::uint64_constant((1u64 << 32) + 7), 7),
        (MachineTerm::int64_constant(-1), u32::MAX),
        (MachineTerm::int64_constant(i64::MIN), 0),
    ] {
        assert_eq!(
            MachineTerm::uint32_from_64(input),
            MachineTerm::constant(expected)
        );
    }
    let x = MachineTerm::Variable(Variable(1));
    for wide in [
        MachineTerm::uint64_from_32(x.clone()),
        MachineTerm::int64_from_32(x.clone()),
        MachineTerm::int64_from_uint32(x.clone()),
        MachineTerm::uint64_from_int32(x.clone()),
    ] {
        assert_eq!(MachineTerm::uint32_from_64(wide), x);
    }
    let narrow = MachineTerm::uint32_from_64(x.clone());
    assert_ne!(narrow, x);
    assert_ne!(MachineTerm::uint64_from_32(narrow), x);
}

#[test]
fn narrowed_shift_bounds_do_not_discard_possible_high_counts() {
    let x = MachineTerm::Variable(Variable(1));
    for count in 0..=64 {
        let narrowed = MachineTerm::uint32_from_64(MachineTerm::uint64_logical_shift_right(
            x.clone(),
            MachineTerm::constant(count),
        ));
        let below = ConditionTerm::unsigned_less_than(narrowed.clone(), MachineTerm::constant(32));
        let above =
            ConditionTerm::unsigned_greater_equal(narrowed.clone(), MachineTerm::constant(32));
        let retained = KernelTerm::retained_machine_operand(
            MachineIntegerType::UInt32,
            MachineOperandView::Legacy(&narrowed),
        );
        let exports = KernelTermExport::machine_export_count();
        for (relation, native) in [
            (CompareRelation::LessThan, &below),
            (CompareRelation::GreaterEqual, &above),
        ] {
            let common = crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::UInt32,
                relation,
                [
                    MachineOperandView::Shared(&retained),
                    MachineOperandView::Legacy(&MachineTerm::constant(32)),
                ],
            );
            assert_eq!(
                matches!(common, ConditionTerm::Constant(true)),
                matches!(native, ConditionTerm::Constant(true)),
                "{count}"
            );
            assert_eq!(
                matches!(common, ConditionTerm::Constant(false)),
                matches!(native, ConditionTerm::Constant(false)),
                "{count}"
            );
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        if (59..64).contains(&count) {
            assert_eq!(below, ConditionTerm::Constant(true));
            assert_eq!(above, ConditionTerm::Constant(false));
        } else {
            assert_ne!(below, ConditionTerm::Constant(true));
            assert_ne!(above, ConditionTerm::Constant(false));
        }
    }
    for mask in [0, 31, 32, u32::MAX] {
        let masked = MachineTerm::bitwise_and(x.clone(), MachineTerm::constant(mask));
        let below = ConditionTerm::unsigned_less_than(masked, MachineTerm::constant(32));
        assert_eq!(below == ConditionTerm::Constant(true), mask < 32);
    }
}

#[test]
fn bitwise_xor_normalizes_swap_identities() {
    let x = MachineTerm::Variable(Variable(1));
    let y = MachineTerm::Variable(Variable(2));
    let x_xor_y = MachineTerm::bitwise_xor(x.clone(), y.clone());
    let recovered_x = MachineTerm::bitwise_xor(y.clone(), x_xor_y.clone());
    let recovered_y = MachineTerm::bitwise_xor(x_xor_y, x.clone());

    assert_eq!(recovered_x, x);
    assert_eq!(recovered_y, y);
}

#[test]
fn floating_point_constant_conversions_round_in_integer_space() {
    let state = ExecutionState::new();
    let cases = [
        (
            crate::kernel::program_expression::cast(
                crate::kernel::program_expression::uint64_literal(16_777_217),
                ProgramType::Float32,
            ),
            ProgramValue::Float32(MachineTerm::constant(0x4b80_0000)),
        ),
        (
            crate::kernel::program_expression::cast(
                crate::kernel::program_expression::uint64_literal(9_007_199_254_740_993),
                ProgramType::Float64,
            ),
            ProgramValue::Float64(MachineTerm::uint64_constant(0x4340_0000_0000_0000)),
        ),
        (
            crate::kernel::program_expression::cast(
                crate::kernel::program_expression::float64_literal(0x3ff0_0000_1000_0000),
                ProgramType::Float32,
            ),
            ProgramValue::Float32(MachineTerm::constant(0x3f80_0000)),
        ),
        (
            crate::kernel::program_expression::cast(
                crate::kernel::program_expression::float32_literal(0x3fc0_0000),
                ProgramType::Float64,
            ),
            ProgramValue::Float64(MachineTerm::uint64_constant(0x3ff8_0000_0000_0000)),
        ),
        (
            crate::kernel::program_expression::cast(
                crate::kernel::program_expression::int64_literal(-16_777_217),
                ProgramType::Float32,
            ),
            ProgramValue::Float32(MachineTerm::constant(0xcb80_0000)),
        ),
    ];

    for (expression, expected) in cases {
        let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
            .expect("constant floating conversion should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::ProgramExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: ExpressionOutcome::Value(expected),
            }
        );
    }
}

#[test]
fn floating_point_to_integer_conversion_truncates_and_rejects_invalid_values() {
    let state = ExecutionState::new();
    let valid = [
        (
            crate::kernel::program_expression::cast(
                crate::kernel::program_expression::float32_literal(0x4070_0000),
                ProgramType::Int32,
            ),
            ProgramValue::Int32(MachineTerm::constant(3)),
        ),
        (
            crate::kernel::program_expression::cast(
                crate::kernel::program_expression::float64_literal(0xc00e_0000_0000_0000),
                ProgramType::Int64,
            ),
            ProgramValue::Int64(MachineTerm::int64_constant(-3)),
        ),
        (
            crate::kernel::program_expression::cast(
                crate::kernel::program_expression::float64_literal(0x8000_0000_0000_0000),
                ProgramType::UInt32,
            ),
            ProgramValue::UInt32(MachineTerm::uint32_constant(0)),
        ),
    ];
    for (expression, expected) in valid {
        let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
            .expect("valid floating-to-integer conversion should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::ProgramExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: ExpressionOutcome::Value(expected),
            }
        );
    }

    for expression in [
        crate::kernel::program_expression::cast(
            crate::kernel::program_expression::float64_literal(0x7ff8_0000_0000_0000),
            ProgramType::Int32,
        ),
        crate::kernel::program_expression::cast(
            crate::kernel::program_expression::float64_literal(0x7ff0_0000_0000_0000),
            ProgramType::Int32,
        ),
        crate::kernel::program_expression::cast(
            crate::kernel::program_expression::float64_literal(0x41e0_0000_0000_0000),
            ProgramType::Int32,
        ),
        crate::kernel::program_expression::cast(
            crate::kernel::program_expression::float64_literal(0x7fef_ffff_ffff_ffff),
            ProgramType::Int64,
        ),
    ] {
        let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
            .expect("invalid floating-to-integer conversion should retain a diagnostic");
        assert_eq!(
            theorem.proposition(),
            &Proposition::ProgramExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch),
            }
        );
    }
}

#[test]
fn floating_point_conditions_follow_ieee_ordering_and_classification() {
    let state = ExecutionState::new();
    let evaluate = |condition| {
        let evaluation = prove_symbolic_program_condition_evaluation(
            state.clone(),
            condition,
            PureFactContext::new(),
        );
        assert_eq!(evaluation.paths().len(), 1);
        match evaluation.paths()[0]
            .theorem()
            .proposition()
            .peel_implications()
        {
            Proposition::ProgramConditionEvaluates {
                outcome: ConditionOutcome::Value(value),
                ..
            } => *value,
            proposition => panic!("unexpected concrete float condition {proposition:?}"),
        }
    };
    let assert_ordering =
        |left: ProgramExpression,
         right: ProgramExpression,
         expected: (bool, bool, bool, bool, bool, bool)| {
            assert_eq!(
                evaluate(crate::kernel::program_expression::less_than(
                    left.clone(),
                    right.clone()
                )),
                expected.0
            );
            assert_eq!(
                evaluate(crate::kernel::program_expression::less_equal(
                    left.clone(),
                    right.clone()
                )),
                expected.1
            );
            assert_eq!(
                evaluate(crate::kernel::program_expression::greater_than(
                    left.clone(),
                    right.clone()
                )),
                expected.2
            );
            assert_eq!(
                evaluate(crate::kernel::program_expression::greater_equal(
                    left.clone(),
                    right.clone()
                )),
                expected.3
            );
            assert_eq!(
                evaluate(crate::kernel::program_expression::equal(
                    left.clone(),
                    right.clone()
                )),
                expected.4
            );
            assert_eq!(
                evaluate(crate::kernel::program_expression::not_equal(left, right)),
                expected.5
            );
        };

    assert_ordering(
        crate::kernel::program_expression::float32_literal(1.0f32.to_bits()),
        crate::kernel::program_expression::float32_literal(2.0f32.to_bits()),
        (true, true, false, false, false, true),
    );
    assert_ordering(
        crate::kernel::program_expression::float64_literal(1.0f64.to_bits()),
        crate::kernel::program_expression::float64_literal(2.0f64.to_bits()),
        (true, true, false, false, false, true),
    );
    assert_ordering(
        crate::kernel::program_expression::float32_literal(0),
        crate::kernel::program_expression::float32_literal(0x8000_0000),
        (false, true, false, true, true, false),
    );
    assert_ordering(
        crate::kernel::program_expression::float64_literal(0),
        crate::kernel::program_expression::float64_literal(0x8000_0000_0000_0000),
        (false, true, false, true, true, false),
    );
    assert_ordering(
        crate::kernel::program_expression::float32_literal(0x7fc0_0000),
        crate::kernel::program_expression::float32_literal(1.0f32.to_bits()),
        (false, false, false, false, false, true),
    );
    assert_ordering(
        crate::kernel::program_expression::float64_literal(0x7ff8_0000_0000_0000),
        crate::kernel::program_expression::float64_literal(1.0f64.to_bits()),
        (false, false, false, false, false, true),
    );

    let classifications = [
        (1.0f32.to_bits(), FloatClassification::Finite),
        (f32::INFINITY.to_bits(), FloatClassification::Infinite),
        (0, FloatClassification::Zero),
        (1, FloatClassification::Subnormal),
        (0x7fc0_0000, FloatClassification::Nan),
    ];
    for (bits, expected_classification) in classifications {
        for classification in [
            FloatClassification::Finite,
            FloatClassification::Infinite,
            FloatClassification::Zero,
            FloatClassification::Subnormal,
            FloatClassification::Nan,
        ] {
            assert_eq!(
                evaluate(crate::kernel::program_expression::float_classification(
                    crate::kernel::program_expression::float32_literal(bits),
                    classification,
                )),
                match expected_classification {
                    FloatClassification::Finite => classification == FloatClassification::Finite,
                    FloatClassification::Zero => matches!(
                        classification,
                        FloatClassification::Finite | FloatClassification::Zero
                    ),
                    FloatClassification::Subnormal => matches!(
                        classification,
                        FloatClassification::Finite | FloatClassification::Subnormal
                    ),
                    _ => classification == expected_classification,
                }
            );
        }
    }
}

#[test]
fn symbolic_floating_conditions_split_and_preserve_float_truthiness() {
    let variable = Variable(901);
    let state = ExecutionState::new().with_local("value", float32(MachineTerm::Variable(variable)));
    let outcomes = |condition| {
        prove_symbolic_program_condition_evaluation(
            state.clone(),
            condition,
            PureFactContext::new(),
        )
        .paths()
        .iter()
        .map(
            |path| match path.theorem().proposition().peel_implications() {
                Proposition::ProgramConditionEvaluates { outcome, .. } => outcome.clone(),
                proposition => panic!("unexpected symbolic float condition {proposition:?}"),
            },
        )
        .collect::<BTreeSet<_>>()
    };
    assert_eq!(
        outcomes(crate::kernel::program_expression::less_than(
            crate::kernel::program_expression::variable("value"),
            crate::kernel::program_expression::float32_literal(1.0f32.to_bits()),
        )),
        BTreeSet::from([
            ConditionOutcome::Value(false),
            ConditionOutcome::Value(true),
        ])
    );
    assert_eq!(
        outcomes(crate::kernel::program_expression::float_classification(
            crate::kernel::program_expression::variable("value"),
            FloatClassification::Nan,
        )),
        BTreeSet::from([
            ConditionOutcome::Value(false),
            ConditionOutcome::Value(true),
        ])
    );
    assert_eq!(
        outcomes(crate::kernel::program_expression::variable("value")),
        BTreeSet::from([
            ConditionOutcome::Value(false),
            ConditionOutcome::Value(true),
        ])
    );
}

#[test]
fn floating_point_arithmetic_rounds_both_widths_in_integer_space() {
    let state = ExecutionState::new();
    let evaluate = |expression| {
        let theorem = prove_program_expression_evaluation(state.clone(), expression)
            .expect("constant floating arithmetic should evaluate");
        match theorem.proposition() {
            Proposition::ProgramExpressionEvaluates { outcome, .. } => outcome.clone(),
            proposition => panic!("unexpected floating arithmetic theorem {proposition:?}"),
        }
    };

    assert_eq!(
        evaluate(crate::kernel::program_expression::add(
            crate::kernel::program_expression::float32_literal(1.0f32.to_bits()),
            crate::kernel::program_expression::float32_literal(2.0f32.to_bits()),
        )),
        ExpressionOutcome::Value(ProgramValue::Float32(MachineTerm::constant(
            3.0f32.to_bits(),
        )))
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::subtract(
            crate::kernel::program_expression::float32_literal(1.0f32.to_bits()),
            crate::kernel::program_expression::float32_literal(2.0f32.to_bits()),
        )),
        ExpressionOutcome::Value(ProgramValue::Float32(MachineTerm::constant(
            (-1.0f32).to_bits(),
        )))
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::multiply(
            crate::kernel::program_expression::float32_literal(1.5f32.to_bits()),
            crate::kernel::program_expression::float32_literal(2.0f32.to_bits()),
        )),
        ExpressionOutcome::Value(ProgramValue::Float32(MachineTerm::constant(
            3.0f32.to_bits(),
        )))
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::divide(
            crate::kernel::program_expression::float32_literal(3.0f32.to_bits()),
            crate::kernel::program_expression::float32_literal(2.0f32.to_bits()),
        )),
        ExpressionOutcome::Value(ProgramValue::Float32(MachineTerm::constant(
            1.5f32.to_bits(),
        )))
    );

    assert_eq!(
        evaluate(crate::kernel::program_expression::add(
            crate::kernel::program_expression::float64_literal(1.0f64.to_bits()),
            crate::kernel::program_expression::float64_literal(2.0f64.to_bits()),
        )),
        ExpressionOutcome::Value(ProgramValue::Float64(MachineTerm::uint64_constant(
            3.0f64.to_bits(),
        )))
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::multiply(
            crate::kernel::program_expression::float64_literal(1.5f64.to_bits()),
            crate::kernel::program_expression::float64_literal(2.0f64.to_bits()),
        )),
        ExpressionOutcome::Value(ProgramValue::Float64(MachineTerm::uint64_constant(
            3.0f64.to_bits(),
        )))
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::divide(
            crate::kernel::program_expression::float64_literal(3.0f64.to_bits()),
            crate::kernel::program_expression::float64_literal(2.0f64.to_bits()),
        )),
        ExpressionOutcome::Value(ProgramValue::Float64(MachineTerm::uint64_constant(
            1.5f64.to_bits(),
        )))
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::float_negate(
            crate::kernel::program_expression::float32_literal(0x8000_0000)
        )),
        ExpressionOutcome::Value(ProgramValue::Float32(MachineTerm::constant(0)))
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::float_negate(
            crate::kernel::program_expression::float64_literal(0)
        )),
        ExpressionOutcome::Value(ProgramValue::Float64(MachineTerm::uint64_constant(
            0x8000_0000_0000_0000,
        )))
    );
}

#[test]
fn floating_point_arithmetic_preserves_ieee_exceptions_and_ties() {
    let state = ExecutionState::new();
    let evaluate = |expression| {
        let theorem = prove_program_expression_evaluation(state.clone(), expression)
            .expect("constant floating arithmetic should evaluate");
        match theorem.proposition() {
            Proposition::ProgramExpressionEvaluates { outcome, .. } => outcome.clone(),
            proposition => panic!("unexpected floating arithmetic theorem {proposition:?}"),
        }
    };
    let f32_value =
        |bits| ExpressionOutcome::Value(ProgramValue::Float32(MachineTerm::constant(bits)));
    let f64_value =
        |bits| ExpressionOutcome::Value(ProgramValue::Float64(MachineTerm::uint64_constant(bits)));

    // The halfway case rounds to the even significand; an exact ulp reaches
    // the next representable value.
    assert_eq!(
        evaluate(crate::kernel::program_expression::add(
            crate::kernel::program_expression::float32_literal(0x3f80_0000),
            crate::kernel::program_expression::float32_literal(0x3380_0000),
        )),
        f32_value(0x3f80_0000)
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::add(
            crate::kernel::program_expression::float32_literal(0x3f80_0000),
            crate::kernel::program_expression::float32_literal(0x3440_0000),
        )),
        f32_value(0x3f80_0002)
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::add(
            crate::kernel::program_expression::float32_literal(0x3f80_0000),
            crate::kernel::program_expression::float32_literal(0x3400_0000),
        )),
        f32_value(0x3f80_0001)
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::add(
            crate::kernel::program_expression::float64_literal(0x3ff0_0000_0000_0000),
            crate::kernel::program_expression::float64_literal(0x3ca0_0000_0000_0000),
        )),
        f64_value(0x3ff0_0000_0000_0000)
    );

    assert_eq!(
        evaluate(crate::kernel::program_expression::add(
            crate::kernel::program_expression::float32_literal(0x7f7f_ffff),
            crate::kernel::program_expression::float32_literal(0x7f7f_ffff),
        )),
        f32_value(0x7f80_0000)
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::add(
            crate::kernel::program_expression::float32_literal(0x7f80_0000),
            crate::kernel::program_expression::float32_literal(0xff80_0000),
        )),
        f32_value(0x7fc0_0000)
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::divide(
            crate::kernel::program_expression::float32_literal(0),
            crate::kernel::program_expression::float32_literal(0),
        )),
        f32_value(0x7fc0_0000)
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::divide(
            crate::kernel::program_expression::float32_literal(0x0080_0000),
            crate::kernel::program_expression::float32_literal(2.0f32.to_bits()),
        )),
        f32_value(0x0040_0000)
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::divide(
            crate::kernel::program_expression::float32_literal(1),
            crate::kernel::program_expression::float32_literal(2.0f32.to_bits()),
        )),
        f32_value(0)
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::divide(
            crate::kernel::program_expression::float64_literal(0x0010_0000_0000_0000),
            crate::kernel::program_expression::float64_literal(2.0f64.to_bits()),
        )),
        f64_value(0x0008_0000_0000_0000)
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::divide(
            crate::kernel::program_expression::float64_literal(1),
            crate::kernel::program_expression::float64_literal(2.0f64.to_bits()),
        )),
        f64_value(0)
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::multiply(
            crate::kernel::program_expression::float32_literal(f32::INFINITY.to_bits()),
            crate::kernel::program_expression::float32_literal(0),
        )),
        f32_value(0x7fc0_0000)
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::divide(
            crate::kernel::program_expression::float64_literal(1.0f64.to_bits()),
            crate::kernel::program_expression::float64_literal(0),
        )),
        f64_value(0x7ff0_0000_0000_0000)
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::divide(
            crate::kernel::program_expression::float64_literal(f64::INFINITY.to_bits()),
            crate::kernel::program_expression::float64_literal(f64::INFINITY.to_bits()),
        )),
        f64_value(0x7ff8_0000_0000_0000)
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::add(
            crate::kernel::program_expression::float64_literal(0x7fef_ffff_ffff_ffff),
            crate::kernel::program_expression::float64_literal(0x7fef_ffff_ffff_ffff),
        )),
        f64_value(0x7ff0_0000_0000_0000)
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::multiply(
            crate::kernel::program_expression::float32_literal(0x8000_0000),
            crate::kernel::program_expression::float32_literal(1.0f32.to_bits()),
        )),
        f32_value(0x8000_0000)
    );
}

#[test]
fn symbolic_floating_arithmetic_remains_typed_and_opaque() {
    let variable = Variable(902);
    let state = ExecutionState::new().with_local("value", float32(MachineTerm::Variable(variable)));
    let expression = crate::kernel::program_expression::add(
        crate::kernel::program_expression::variable("value"),
        crate::kernel::program_expression::float32_literal(1.0f32.to_bits()),
    );
    let theorem =
        prove_program_expression_evaluation(state, expression).expect("symbolic float add");
    let Proposition::ProgramExpressionEvaluates {
        outcome: ExpressionOutcome::Value(ProgramValue::Float32(term)),
        ..
    } = theorem.proposition()
    else {
        panic!("symbolic float addition should produce a float value");
    };
    assert!(matches!(term, MachineTerm::Float32Binary { .. }));
}

#[test]
fn mixed_floating_arithmetic_promotes_to_the_wider_or_present_float_type() {
    let state = ExecutionState::new();
    let evaluate = |expression| {
        let theorem = prove_program_expression_evaluation(state.clone(), expression)
            .expect("mixed floating arithmetic should evaluate");
        match theorem.proposition() {
            Proposition::ProgramExpressionEvaluates { outcome, .. } => outcome.clone(),
            proposition => panic!("unexpected mixed floating theorem {proposition:?}"),
        }
    };

    assert_eq!(
        evaluate(crate::kernel::program_expression::add(
            crate::kernel::program_expression::float32_literal(1.5f32.to_bits()),
            crate::kernel::program_expression::float64_literal(2.0f64.to_bits()),
        )),
        ExpressionOutcome::Value(ProgramValue::Float64(MachineTerm::uint64_constant(
            3.5f64.to_bits(),
        )))
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::add(
            crate::kernel::program_expression::float32_literal(1.5f32.to_bits()),
            crate::kernel::program_expression::int32_literal(2)
        )),
        ExpressionOutcome::Value(ProgramValue::Float32(MachineTerm::constant(
            3.5f32.to_bits(),
        )))
    );
    assert_eq!(
        evaluate(crate::kernel::program_expression::less_than(
            crate::kernel::program_expression::float64_literal(1.0f64.to_bits()),
            crate::kernel::program_expression::int32_literal(2),
        )),
        ExpressionOutcome::Value(ProgramValue::Int32(MachineTerm::constant(1)))
    );
}

#[test]
fn symbolic_float_conversions_remain_typed_and_float_to_integer_is_guarded() {
    let f32_variable = Variable(903);
    let f64_variable = Variable(904);
    let integer_variable = Variable(905);
    let state = ExecutionState::new()
        .with_local("f32", float32(MachineTerm::Variable(f32_variable)))
        .with_local("f64", float64(MachineTerm::Variable(f64_variable)))
        .with_local("integer", int32(MachineTerm::Variable(integer_variable)));

    let theorem = prove_program_expression_evaluation(
        state.clone(),
        crate::kernel::program_expression::cast(
            crate::kernel::program_expression::variable("integer"),
            ProgramType::Float64,
        ),
    )
    .expect("symbolic integer-to-float conversion should evaluate");
    let Proposition::ProgramExpressionEvaluates {
        outcome: ExpressionOutcome::Value(ProgramValue::Float64(term)),
        ..
    } = theorem.proposition()
    else {
        panic!("symbolic integer-to-float conversion should produce a double");
    };
    assert!(matches!(term, MachineTerm::PureFunctionApplication { .. }));

    let theorem = prove_program_expression_evaluation(
        state.clone(),
        crate::kernel::program_expression::cast(
            crate::kernel::program_expression::variable("f32"),
            ProgramType::Float64,
        ),
    )
    .expect("symbolic float widening conversion should evaluate");
    let Proposition::ProgramExpressionEvaluates {
        outcome: ExpressionOutcome::Value(ProgramValue::Float64(term)),
        ..
    } = theorem.proposition()
    else {
        panic!("symbolic float widening conversion should produce a double");
    };
    assert!(matches!(term, MachineTerm::PureFunctionApplication { .. }));

    let paths = evaluate_program_expression_paths(
        &state,
        &crate::kernel::program_expression::cast(
            crate::kernel::program_expression::variable("f64"),
            ProgramType::Int32,
        ),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .expect("symbolic float-to-integer conversion should retain its guard");
    assert_eq!(paths.len(), 1);
    assert!(matches!(
        paths[0].outcome,
        ExpressionOutcome::Value(ProgramValue::Int32(
            MachineTerm::PureFunctionApplication { .. }
        ))
    ));
    assert_eq!(paths[0].obligations.len(), 3);
}

#[test]
fn signed_add_overflow_is_native_undefined_behavior() {
    let state = ExecutionState::new();
    let theorem = prove_program_expression_evaluation(
        state.clone(),
        crate::kernel::program_expression::add(
            crate::kernel::program_expression::int32_literal(2_147_483_647),
            crate::kernel::program_expression::int32_literal(1),
        ),
    )
    .expect("concrete add should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramExpressionEvaluates {
            state: Box::new(state),
            expression: crate::kernel::program_expression::add(
                crate::kernel::program_expression::int32_literal(2_147_483_647),
                crate::kernel::program_expression::int32_literal(1)
            ),
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::SignedOverflow),
        }
    );
}

#[test]
fn wide_shift_counts_are_checked_before_narrowing() {
    for (count_case, count_value_bits) in [2_u64, 0x1_0000_0002].into_iter().enumerate() {
        for shift_left in [false, true] {
            for left_is_64_bit in [false, true] {
                for unsigned_count in [false, true] {
                    let count_variable = Variable(
                        93_900
                            + count_case as u64 * 8
                            + u64::from(shift_left) * 4
                            + u64::from(left_is_64_bit) * 2
                            + u64::from(unsigned_count),
                    );
                    let count_term = MachineTerm::Variable(count_variable);
                    let (count_value, count_type, count_fact) = if unsigned_count {
                        (
                            ProgramValue::UInt64(count_term.clone()),
                            ProgramType::UInt64,
                            ConditionTerm::uint64_equal(
                                count_term.clone(),
                                MachineTerm::uint64_constant(count_value_bits),
                            ),
                        )
                    } else {
                        (
                            ProgramValue::Int64(count_term.clone()),
                            ProgramType::Int64,
                            ConditionTerm::int64_equal(
                                count_term.clone(),
                                MachineTerm::int64_constant(count_value_bits as i64),
                            ),
                        )
                    };
                    let (left_value, left_type) = if left_is_64_bit {
                        (
                            ProgramValue::Int64(MachineTerm::int64_constant(1)),
                            ProgramType::Int64,
                        )
                    } else {
                        (
                            ProgramValue::Int32(MachineTerm::constant(1)),
                            ProgramType::Int32,
                        )
                    };
                    let mut state = ExecutionState::new()
                        .with_local("left", left_value.clone())
                        .with_local("count", count_value.clone());
                    state.locals.set_typed("left", left_value, left_type);
                    state.locals.set_typed("count", count_value, count_type);

                    let left = crate::kernel::program_expression::variable("left");
                    let right = crate::kernel::program_expression::variable("count");
                    let expression = if shift_left {
                        crate::kernel::program_expression::shift_left(left, right)
                    } else {
                        crate::kernel::program_expression::shift_right(left, right)
                    };
                    let assumptions = PureFactContext::new().assume_condition(count_fact, true);
                    let paths = evaluate_program_expression_paths(
                        &state,
                        &expression,
                        &assumptions,
                        &mut ExecutionBudget::for_program_expression(&expression),
                    )
                    .expect("wide shift evaluation should stay within its execution budget");

                    if count_value_bits == 2 {
                        assert!(
                            paths
                                .iter()
                                .any(|path| matches!(path.outcome, ExpressionOutcome::Value(_))),
                            "in-range count unexpectedly lost its value path"
                        );
                        assert!(
                            !paths.iter().any(|path| matches!(
                                path.outcome,
                                ExpressionOutcome::UndefinedBehavior(
                                    UndefinedBehavior::InvalidShift
                                )
                            )),
                            "in-range count was reported as undefined behavior"
                        );
                    } else {
                        assert!(
                            paths.iter().any(|path| matches!(
                                path.outcome,
                                ExpressionOutcome::UndefinedBehavior(
                                    UndefinedBehavior::InvalidShift
                                )
                            )),
                            "left_shift={shift_left}, left64={left_is_64_bit}, unsigned_count={unsigned_count}: {paths:?}"
                        );
                        assert!(
                            !paths
                                .iter()
                                .any(|path| matches!(path.outcome, ExpressionOutcome::Value(_))),
                            "an out-of-range 64-bit count must not be accepted via its low word"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn condition_evaluation_certifies_c_truthiness_directly() {
    let state = ExecutionState::new();
    let condition = crate::kernel::program_expression::less_than(
        crate::kernel::program_expression::int32_literal(1),
        crate::kernel::program_expression::int32_literal(2),
    );
    let evaluation = prove_symbolic_program_condition_evaluation(
        state.clone(),
        condition.clone(),
        PureFactContext::new(),
    );

    assert_eq!(evaluation.paths().len(), 1);
    assert_eq!(
        evaluation.paths()[0]
            .theorem()
            .proposition()
            .peel_implications(),
        &Proposition::ProgramConditionEvaluates {
            state: Box::new(state),
            condition,
            outcome: ConditionOutcome::Value(true),
        }
    );
}

#[test]
fn void_truthiness_is_an_explicit_type_error() {
    let state = ExecutionState::new();
    let condition = program_void_value();
    let evaluation = prove_symbolic_program_condition_evaluation(
        state.clone(),
        condition.clone(),
        PureFactContext::new(),
    );

    assert_eq!(evaluation.paths().len(), 1);
    assert_eq!(
        evaluation.paths()[0]
            .theorem()
            .proposition()
            .peel_implications(),
        &Proposition::ProgramConditionEvaluates {
            state: Box::new(state.clone()),
            condition,
            outcome: ConditionOutcome::RuntimeError(RuntimeError::TypeMismatch),
        }
    );

    for expression in [
        crate::kernel::program_expression::not(program_void_value()),
        crate::kernel::program_expression::and(
            program_void_value(),
            crate::kernel::program_expression::int32_literal(1),
        ),
        crate::kernel::program_expression::or(
            program_void_value(),
            crate::kernel::program_expression::int32_literal(1),
        ),
    ] {
        let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
            .expect("invalid void truthiness should retain its runtime-error frontier");
        assert_eq!(
            theorem.proposition(),
            &Proposition::ProgramExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch),
            }
        );
    }
}

#[test]
fn void_local_declaration_is_an_explicit_type_error() {
    let paths = execute_execution_statement_paths(
        &ExecutionState::new(),
        &program_declare("invalid", ProgramType::Void),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("invalid void declarations should execute to a type error");

    assert_eq!(paths.len(), 1);
    assert_eq!(
        &paths[0].outcome,
        &StatementOutcome::RuntimeError(RuntimeError::TypeMismatch)
    );

    let paths = execute_execution_statement_paths(
        &ExecutionState::new(),
        &program_if(
            program_void_value(),
            ProgramStatement::Skip,
            ProgramStatement::Skip,
        ),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("a void condition should execute to a type error");
    assert_eq!(paths.len(), 1);
    assert_eq!(
        &paths[0].outcome,
        &StatementOutcome::RuntimeError(RuntimeError::TypeMismatch)
    );
}

#[test]
fn symbolic_condition_evaluation_exposes_both_truthiness_paths() {
    let x = Variable(90);
    let state = ExecutionState::new().with_local("x", int32(MachineTerm::Variable(x)));
    let condition = crate::kernel::program_expression::greater_equal(
        crate::kernel::program_expression::variable("x"),
        crate::kernel::program_expression::int32_literal(0),
    );
    let evaluation =
        prove_symbolic_program_condition_evaluation(state, condition, PureFactContext::new());

    let outcomes = evaluation
        .paths()
        .iter()
        .map(
            |path| match path.theorem().proposition().peel_implications() {
                Proposition::ProgramConditionEvaluates { outcome, .. } => outcome.clone(),
                proposition => panic!("unexpected condition theorem {proposition:?}"),
            },
        )
        .collect::<BTreeSet<_>>();
    assert_eq!(
        outcomes,
        BTreeSet::from([
            ConditionOutcome::Value(false),
            ConditionOutcome::Value(true),
        ])
    );
}

#[test]
fn int32_subtraction_is_native() {
    let state = ExecutionState::new();
    let statement = program_return(crate::kernel::program_expression::subtract(
        crate::kernel::program_expression::int32_literal(7),
        crate::kernel::program_expression::int32_literal(2),
    ));
    let theorem =
        prove_symbolic_program_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("concrete subtraction should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramStatementExecutes {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(5).into(),
                state: Box::new(state),
            },
        }
    );
}

#[test]
fn nonnegative_ordered_subtraction_does_not_overflow() {
    let position = MachineTerm::Variable(Variable(24));
    let length = MachineTerm::Variable(Variable(25));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(position.clone(), MachineTerm::constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(length.clone(), position.clone()),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_subtract_overflows(length, position)),
        Some(false)
    );
}

#[test]
fn signed_subtract_overflow_is_native_undefined_behavior() {
    let state = ExecutionState::new();
    let theorem = prove_program_expression_evaluation(
        state.clone(),
        crate::kernel::program_expression::subtract(
            crate::kernel::program_expression::int32_literal(2_147_483_648),
            crate::kernel::program_expression::int32_literal(1),
        ),
    )
    .expect("concrete subtraction should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramExpressionEvaluates {
            state: Box::new(state),
            expression: crate::kernel::program_expression::subtract(
                crate::kernel::program_expression::int32_literal(2_147_483_648),
                crate::kernel::program_expression::int32_literal(1)
            ),
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::SignedOverflow),
        }
    );
}

#[test]
fn int32_comparisons_return_c_int32_zero_or_one() {
    let state = ExecutionState::new();
    let examples = [
        (
            crate::kernel::program_expression::less_equal(
                crate::kernel::program_expression::int32_literal(2),
                crate::kernel::program_expression::int32_literal(2),
            ),
            int32(1),
        ),
        (
            crate::kernel::program_expression::greater_than(
                crate::kernel::program_expression::int32_literal(3),
                crate::kernel::program_expression::int32_literal(2),
            ),
            int32(1),
        ),
        (
            crate::kernel::program_expression::greater_equal(
                crate::kernel::program_expression::int32_literal(2),
                crate::kernel::program_expression::int32_literal(3),
            ),
            int32(0),
        ),
        (
            crate::kernel::program_expression::equal(
                crate::kernel::program_expression::int32_literal(4),
                crate::kernel::program_expression::int32_literal(4),
            ),
            int32(1),
        ),
    ];

    for (expression, expected) in examples {
        let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
            .expect("comparison should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::ProgramExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: ExpressionOutcome::Value(expected),
            }
        );
    }
}

#[test]
fn pointer_equality_returns_c_int32_zero_or_one() {
    let p = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let same = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let next = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let other = Pointer {
        block: "other".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(p))
        .with_local("same", ProgramValue::pointer(same))
        .with_local("next", ProgramValue::pointer(next))
        .with_local("other", ProgramValue::pointer(other));
    let examples = [
        (
            crate::kernel::program_expression::equal(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::variable("same"),
            ),
            int32(1),
        ),
        (
            crate::kernel::program_expression::equal(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::variable("next"),
            ),
            int32(0),
        ),
        (
            crate::kernel::program_expression::equal(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::variable("other"),
            ),
            int32(0),
        ),
    ];

    for (expression, expected) in examples {
        let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
            .expect("pointer equality should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::ProgramExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: ExpressionOutcome::Value(expected),
            }
        );
    }
}

#[test]
fn pointer_values_preserve_their_exact_c_types_without_changing_address_identity() {
    let address = Pointer {
        block: "same-address".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let int32_pointer = ProgramValue::typed_pointer(address.clone(), ProgramType::Int32Pointer);
    let uint8_pointer = ProgramValue::typed_pointer(address.clone(), ProgramType::UInt8Pointer);

    assert_eq!(int32_pointer.program_type(), ProgramType::Int32Pointer);
    assert_eq!(uint8_pointer.program_type(), ProgramType::UInt8Pointer);
    let ProgramValue::Pointer(int32_pointer) = int32_pointer else {
        unreachable!();
    };
    let ProgramValue::Pointer(uint8_pointer) = uint8_pointer else {
        unreachable!();
    };
    assert_eq!(int32_pointer.pointer(), uint8_pointer.pointer());
}

#[test]
fn explicit_wide_integer_pointer_cast_accepts_only_proven_null_without_origin() {
    let word = MachineTerm::Variable(Variable(4242));
    for value in [
        ProgramValue::UInt64(word.clone()),
        ProgramValue::Int64(word.clone()),
    ] {
        for known_value in [None, Some(0), Some(4)] {
            let mut assumptions = PureFactContext::new();
            if let Some(known) = known_value {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::uint64_equal(word.clone(), MachineTerm::uint64_constant(known)),
                    true,
                );
            }
            let mut obligations = Vec::new();
            let cast = crate::kernel::eval::cast_program_value_to_type(
                value.clone(),
                ProgramType::UInt8Pointer,
                crate::kernel::eval::IntegerConversion::Modular,
                &mut obligations,
                &assumptions,
            );
            if known_value == Some(0) {
                assert_eq!(
                    cast.unwrap(),
                    ProgramValue::typed_pointer(Pointer::null(), ProgramType::UInt8Pointer),
                );
            } else {
                assert!(matches!(cast, Err(RuntimeError::PointerConversion(_))));
            }
            // An unknown integer must not acquire a pointer by leaving an
            // unproved null obligation behind.
            assert!(obligations.is_empty());
        }
    }
}

#[test]
fn pointer_cast_retags_the_view_but_pointer_type_mismatch_is_not_implicit() {
    let address = Pointer {
        block: "typed-pointer".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut state = ExecutionState::new();
    state.locals.set_typed_with_all_qualifiers(
        "int32_p",
        ProgramValue::typed_pointer_with_pointee_constant(
            address.clone(),
            ProgramType::Int32Pointer,
            true,
        ),
        ProgramType::Int32Pointer,
        false,
        false,
        false,
        true,
    );
    state.locals.set_typed(
        "uint8_p",
        ProgramValue::pointer(address.clone()),
        ProgramType::UInt8Pointer,
    );

    let cast = crate::kernel::program_expression::cast(
        crate::kernel::program_expression::variable("int32_p"),
        ProgramType::UInt8Pointer,
    );
    let cast_theorem = prove_program_expression_evaluation(state.clone(), cast.clone())
        .expect("an explicit pointer cast should evaluate");
    let Proposition::ProgramExpressionEvaluates {
        outcome: ExpressionOutcome::Value(value),
        ..
    } = cast_theorem.proposition()
    else {
        panic!("explicit pointer cast did not produce a value");
    };
    assert_eq!(value.program_type(), ProgramType::UInt8Pointer);
    let ProgramValue::Pointer(value) = value else {
        unreachable!();
    };
    assert_eq!(value.pointer(), &address);
    assert!(
        value.pointee_constant(),
        "a byte view must retain source const qualification"
    );
    let (spec_value, _) = program_evaluate_speprogram_expression_at_state(
        &state,
        &SpecExpression::Cast(
            Box::new(SpecExpression::Value(
                ProgramValue::typed_pointer_with_pointee_constant(
                    address.clone(),
                    ProgramType::Int32Pointer,
                    true,
                ),
            )),
            ProgramType::UInt8Pointer,
        ),
        None,
        &PureFactContext::new(),
    )
    .unwrap();
    let ProgramValue::Pointer(spec_pointer) = spec_value else {
        panic!("byte-view spec cast must yield a pointer");
    };
    assert_eq!(spec_pointer.pointer(), &address);
    assert!(spec_pointer.pointee_constant());

    let equality = crate::kernel::program_expression::equal(
        crate::kernel::program_expression::variable("int32_p"),
        crate::kernel::program_expression::variable("uint8_p"),
    );
    let equality_theorem = prove_program_expression_evaluation(state, equality.clone())
        .expect("a mismatched pointer comparison should retain its error frontier");
    assert!(matches!(
        equality_theorem.proposition(),
        Proposition::ProgramExpressionEvaluates {
            expression,
            outcome: ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch),
            ..
        } if expression == &equality
    ));
}

#[test]
fn spec_pointer_equality_lowers_to_a_pure_fact() {
    let left = Pointer::symbolic(Variable(22_100));
    let right = Pointer::symbolic(Variable(22_101));
    let equality = ConditionTerm::PointerValueEqual(
        Box::new(PointerValue::new(left.clone(), ProgramType::Int32Pointer)),
        Box::new(PointerValue::new(right.clone(), ProgramType::Int32Pointer)),
    );

    assert_eq!(
        program_value_comparison_proposition(
            &ProgramValue::pointer(left.clone()),
            ComparisonOperator::Equal,
            &ProgramValue::pointer(right.clone()),
        ),
        Some(Proposition::ConditionIs(equality.clone(), true)),
    );
    assert_eq!(
        program_value_comparison_proposition(
            &ProgramValue::pointer(left.clone()),
            ComparisonOperator::NotEqual,
            &ProgramValue::pointer(right),
        ),
        Some(Proposition::ConditionIs(equality, false)),
    );
    assert_eq!(
        program_value_comparison_proposition(
            &ProgramValue::pointer(left),
            ComparisonOperator::LessThan,
            &ProgramValue::Int32(MachineTerm::constant(0)),
        ),
        None,
    );
}

#[test]
fn finite_float_context_proves_reflexive_comparisons() {
    let value = MachineTerm::Variable(Variable(22_102));
    let finite = ConditionTerm::float64_classification(value.clone(), FloatClassification::Finite);
    let assumptions = PureFactContext::new().assume_condition(finite, true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::float64_compare(
            value.clone(),
            value.clone(),
            ComparisonOperator::Equal,
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::float64_compare(
            value.clone(),
            value,
            ComparisonOperator::NotEqual,
        )),
        Some(false)
    );
}

#[test]
fn finite_structural_float_read_proves_reflexive_comparison() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = crate::kernel::intern_memory(Memory::new());
    let pointer = Pointer::symbolic(Variable(22_103));
    let value = crate::kernel::eval::scalar_read_for_exact_cell(
        &memory,
        &pointer,
        crate::kernel::LoadKind::Float64,
        8,
    );
    let finite = ConditionTerm::float64_classification(value.clone(), FloatClassification::Finite);
    let assumptions = PureFactContext::new().assume_condition(finite.clone(), true);
    assert_eq!(assumptions.decide(&finite), Some(true), "held finiteness");
    assert_eq!(
        assumptions.decide(&ConditionTerm::float64_compare(
            value.clone(),
            value,
            ComparisonOperator::Equal,
        )),
        Some(true)
    );
}

#[test]
fn spec_pointer_order_lowers_same_block_offsets() {
    let left = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    assert_eq!(
        program_value_comparison_proposition(
            &ProgramValue::pointer(left),
            ComparisonOperator::LessThan,
            &ProgramValue::pointer(right),
        ),
        Some(Proposition::ConditionIs(
            ConditionTerm::Constant(true),
            true,
        )),
    );
}

#[test]
fn symbolic_pointer_truthiness_keeps_null_and_nonnull_paths() {
    let paths = program_truthiness_paths(
        ProgramValue::pointer(Pointer::symbolic(Variable(22_000))),
        Vec::new().into(),
        Vec::new(),
        &PureFactContext::new(),
    );

    assert_eq!(paths.len(), 2);
    assert!(paths.iter().any(|path| path.is_true));
    assert!(paths.iter().any(|path| !path.is_true));
}

#[test]
fn pointer_equality_accepts_int32_zero_as_null_pointer_constant() {
    let null = Pointer {
        block: "null".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let nonnull = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new()
        .with_local("nullp", ProgramValue::pointer(null))
        .with_local("p", ProgramValue::pointer(nonnull));
    let examples = [
        (
            crate::kernel::program_expression::equal(
                crate::kernel::program_expression::variable("nullp"),
                crate::kernel::program_expression::int32_literal(0),
            ),
            int32(1),
        ),
        (
            crate::kernel::program_expression::equal(
                crate::kernel::program_expression::int32_literal(0),
                crate::kernel::program_expression::variable("nullp"),
            ),
            int32(1),
        ),
        (
            crate::kernel::program_expression::equal(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(0),
            ),
            int32(0),
        ),
    ];

    for (expression, expected) in examples {
        let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
            .expect("null equality should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::ProgramExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: ExpressionOutcome::Value(expected),
            }
        );
    }

    let invalid = crate::kernel::program_expression::equal(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(1),
    );
    let theorem = prove_program_expression_evaluation(state.clone(), invalid.clone())
        .expect("invalid pointer equality should evaluate");
    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramExpressionEvaluates {
            state: Box::new(state),
            expression: invalid,
            outcome: ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch),
        }
    );
}

#[test]
fn not_equal_and_not_return_c_int32_zero_or_one() {
    let null = Pointer {
        block: "null".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let p = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let same = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let next = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let state = ExecutionState::new()
        .with_local("nullp", ProgramValue::pointer(null))
        .with_local("p", ProgramValue::pointer(p))
        .with_local("same", ProgramValue::pointer(same))
        .with_local("next", ProgramValue::pointer(next));
    let examples = [
        (
            crate::kernel::program_expression::not_equal(
                crate::kernel::program_expression::int32_literal(4),
                crate::kernel::program_expression::int32_literal(5),
            ),
            int32(1),
        ),
        (
            crate::kernel::program_expression::not_equal(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::variable("same"),
            ),
            int32(0),
        ),
        (
            crate::kernel::program_expression::not_equal(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::variable("next"),
            ),
            int32(1),
        ),
        (
            crate::kernel::program_expression::not_equal(
                crate::kernel::program_expression::variable("nullp"),
                crate::kernel::program_expression::int32_literal(0),
            ),
            int32(0),
        ),
        (
            crate::kernel::program_expression::not(
                crate::kernel::program_expression::int32_literal(0),
            ),
            int32(1),
        ),
        (
            crate::kernel::program_expression::not(
                crate::kernel::program_expression::int32_literal(7),
            ),
            int32(0),
        ),
        (
            crate::kernel::program_expression::not(crate::kernel::program_expression::variable(
                "nullp",
            )),
            int32(1),
        ),
        (
            crate::kernel::program_expression::not(crate::kernel::program_expression::variable(
                "p",
            )),
            int32(0),
        ),
    ];

    for (expression, expected) in examples {
        let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
            .expect("logical expression should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::ProgramExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: ExpressionOutcome::Value(expected),
            }
        );
    }
}

#[test]
fn logical_and_or_short_circuit_right_operand() {
    let invalid_pointer = Pointer {
        block: "missing".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let invalid_load = crate::kernel::program_expression::typed_load(
        crate::kernel::program_expression::pointer_value(invalid_pointer),
        ProgramType::Int32,
    );
    let state = ExecutionState::new().with_resource_context(view_memory_context(
        Pointer {
            block: "missing".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0,
        1,
    ));
    let examples = [
        (
            crate::kernel::program_expression::and(
                crate::kernel::program_expression::int32_literal(0),
                invalid_load.clone(),
            ),
            int32(0),
        ),
        (
            crate::kernel::program_expression::or(
                crate::kernel::program_expression::int32_literal(1),
                invalid_load.clone(),
            ),
            int32(1),
        ),
    ];

    for (expression, expected) in examples {
        let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
            .expect("short-circuit expression should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::ProgramExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: ExpressionOutcome::Value(expected),
            }
        );
    }

    assert!(
        prove_program_expression_evaluation(
            state.clone(),
            crate::kernel::program_expression::and(
                crate::kernel::program_expression::int32_literal(1),
                invalid_load.clone()
            ),
        )
        .is_none()
    );
    assert!(
        prove_program_expression_evaluation(
            state,
            crate::kernel::program_expression::or(
                crate::kernel::program_expression::int32_literal(0),
                invalid_load
            )
        )
        .is_none()
    );
}

#[test]
fn void_pointer_dereferences_report_indeterminate_pointee_type() {
    let pointer = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let pointer_value = || {
        crate::kernel::program_expression::typed_pointer_value(
            pointer.clone(),
            ProgramType::VoidPointer,
        )
    };
    let expressions = [
        crate::kernel::program_expression::load(pointer_value()),
        crate::kernel::program_expression::index(
            pointer_value(),
            crate::kernel::program_expression::int32_literal(1),
        ),
    ];

    for expression in expressions {
        let theorem =
            prove_program_expression_evaluation(ExecutionState::new(), expression.clone())
                .expect("a void-pointer dereference should produce an explicit model error");
        assert_eq!(
            theorem.proposition(),
            &Proposition::ProgramExpressionEvaluates {
                state: Box::new(ExecutionState::new()),
                expression,
                outcome: ExpressionOutcome::RuntimeError(RuntimeError::IndeterminatePointeeType,),
            }
        );
    }
}

#[test]
fn captured_typed_pointer_load_requires_read_authority() {
    let pointer = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new();
    let expression = crate::kernel::program_expression::load(
        crate::kernel::program_expression::pointer_value(pointer.clone()),
    );
    let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
        .expect("a typed pointer without a view should report the missing authority");
    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: ExpressionOutcome::RuntimeError(RuntimeError::MissingResource {
                resource: Box::new(view_memory_fact(pointer, 0, 1)),
            }),
        }
    );
}

#[test]
fn captured_void_pointer_arithmetic_retains_the_gnu_byte_stride() {
    let pointer = Pointer {
        block: "bytes".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new().with_memory(Memory::new().with_block("bytes", 8));
    let value = || {
        crate::kernel::program_expression::typed_pointer_value(
            pointer.clone(),
            ProgramType::VoidPointer,
        )
    };
    for expression in [
        crate::kernel::program_expression::add(
            value(),
            crate::kernel::program_expression::int32_literal(1),
        ),
        crate::kernel::program_expression::add(
            crate::kernel::program_expression::int32_literal(1),
            value(),
        ),
    ] {
        let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
            .expect("GNU void-pointer arithmetic uses a byte stride inside live storage");
        assert_eq!(
            theorem.proposition(),
            &Proposition::ProgramExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: ExpressionOutcome::Value(ProgramValue::typed_pointer(
                    pointer.offset_by_bytes(1),
                    ProgramType::VoidPointer,
                )),
            }
        );
    }
}

#[test]
fn function_pointer_operations_report_indeterminate_pointee_type() {
    let pointer = Pointer::function("callback");
    let function_type = ProgramType::FunctionPointer(ProgramType::function_pointer_signature(
        ProgramType::Int32,
        &[ProgramType::Int32],
    ));
    let mut state = ExecutionState::new();
    state
        .locals
        .set_typed("callback", ProgramValue::pointer(pointer), function_type);
    let expressions = [
        crate::kernel::program_expression::load(crate::kernel::program_expression::variable(
            "callback",
        )),
        crate::kernel::program_expression::add(
            crate::kernel::program_expression::variable("callback"),
            crate::kernel::program_expression::int32_literal(1),
        ),
        crate::kernel::program_expression::pointer_offset_bytes(
            crate::kernel::program_expression::variable("callback"),
            4,
        ),
    ];

    for expression in expressions {
        let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
            .expect("a function-pointer object operation should produce a model error");
        assert_eq!(
            theorem.proposition(),
            &Proposition::ProgramExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: ExpressionOutcome::RuntimeError(RuntimeError::IndeterminatePointeeType),
            }
        );
    }
}

#[test]
fn symbolic_pointer_equality_reports_branch_facts() {
    let offset = Variable(80);
    let left = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Variable(offset),
    };
    // A C comparison states that the addresses are equal, not the pointers.
    let condition =
        crate::kernel::eval::program_pointer_comparison_condition(left.clone(), right.clone());
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(left))
        .with_local("q", ProgramValue::pointer(right));
    let statement = program_if(
        crate::kernel::program_expression::equal(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::variable("q"),
        ),
        program_return(crate::kernel::program_expression::int32_literal(1)),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    );
    let execution = prove_symbolic_program_execution_paths(
        state.clone(),
        statement.clone(),
        PureFactContext::new(),
    );

    assert_eq!(execution.paths().len(), 2);
    assert_eq!(
        execution.paths()[0].facts(),
        &[ExecutionPureFact::condition(condition.clone(), true)]
    );
    assert_eq!(
        execution.paths()[0]
            .theorem()
            .proposition()
            .peel_implications(),
        &Proposition::ProgramStatementExecutes {
            state: Box::new(state.clone()),
            statement: Box::new(statement.clone()),
            outcome: StatementOutcome::Return {
                value: int32(1).into(),
                state: Box::new(state.clone()),
            },
        }
    );
    assert_eq!(
        execution.paths()[1].facts(),
        &[ExecutionPureFact::condition(condition, false)]
    );
    assert_eq!(
        execution.paths()[1]
            .theorem()
            .proposition()
            .peel_implications(),
        &Proposition::ProgramStatementExecutes {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(0).into(),
                state: Box::new(state),
            },
        }
    );
}

#[test]
fn if_uses_c_int32_truthiness() {
    let state = ExecutionState::new();
    let statement = program_if(
        crate::kernel::program_expression::int32_literal(7),
        program_return(crate::kernel::program_expression::int32_literal(1)),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    );
    let theorem =
        prove_symbolic_program_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("nonzero int32 condition should take then branch");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramStatementExecutes {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(1).into(),
                state: Box::new(state),
            },
        }
    );

    let state = ExecutionState::new();
    let statement = program_if(
        crate::kernel::program_expression::int32_literal(0),
        program_return(crate::kernel::program_expression::int32_literal(1)),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    );
    let theorem =
        prove_symbolic_program_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("zero int32 condition should take else branch");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramStatementExecutes {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(0).into(),
                state: Box::new(state),
            },
        }
    );
}

#[test]
fn assignment_and_sequence_update_native_state() {
    let state = ExecutionState::new().with_local("x", int32(0));
    let statement = program_seq(
        program_assign("x", crate::kernel::program_expression::int32_literal(2)),
        program_return(crate::kernel::program_expression::variable("x")),
    );
    let final_state = ExecutionState::new().with_local("x", int32(2));
    let theorem =
        prove_symbolic_program_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("assignment sequence should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramStatementExecutes {
            state: Box::new(state),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(2).into(),
                state: Box::new(final_state),
            },
        }
    );
}

#[test]
fn store_then_load_threads_native_memory() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let resources = own_memory_context(pointer.clone(), 0, 1);
    let state = ExecutionState::new().with_resource_context(resources.clone());
    let statement = program_seq(
        program_typed_store(
            crate::kernel::program_expression::pointer_value(pointer.clone()),
            crate::kernel::program_expression::int32_literal(9),
            ProgramType::Int32,
        ),
        program_return(crate::kernel::program_expression::typed_load(
            crate::kernel::program_expression::pointer_value(pointer.clone()),
            ProgramType::Int32,
        )),
    );
    let final_state = ExecutionState::new()
        .with_memory(Memory::new().store(pointer.clone(), int32(9)))
        .with_resource_context(resources);
    let theorem =
        prove_symbolic_program_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("store then load should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramStatementExecutes {
            state: Box::new(state),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(9).into(),
                state: Box::new(final_state),
            },
        }
    );
}

#[test]
fn viewed_memory_resource_permits_symbolic_external_load_from_incomplete_memory() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(pointer.clone()))
        .with_resource_context(view_memory_context(pointer.clone(), 0, 1));
    let statement = program_return(crate::kernel::program_expression::load(
        crate::kernel::program_expression::variable("p"),
    ));
    let execution = prove_symbolic_program_execution_paths(
        state.clone(),
        statement.clone(),
        PureFactContext::new(),
    );

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(execution.paths()[0].obligations(), &[]);
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::ProgramStatementExecutes {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                // The symbolic read is canonical at creation: its load
                // variable, which names this load.
                value: int32(crate::kernel::canonical_term(&MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(Memory::new()),
                    Box::new(pointer),
                    crate::kernel::LoadKind::Int32,
                )))
                .into(),
                state: Box::new(state),
            },
        }
    );
}

#[test]
fn block_backed_store_then_load_needs_no_memory_obligation() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = Memory::new().with_block("block", 16);
    let resources = own_memory_context(pointer.clone(), 0, 1);
    let state = ExecutionState::new()
        .with_memory(memory.clone())
        .with_resource_context(resources.clone());
    let statement = program_seq(
        program_typed_store(
            crate::kernel::program_expression::pointer_value(pointer.clone()),
            crate::kernel::program_expression::int32_literal(9),
            ProgramType::Int32,
        ),
        program_return(crate::kernel::program_expression::typed_load(
            crate::kernel::program_expression::pointer_value(pointer.clone()),
            ProgramType::Int32,
        )),
    );
    let final_state = ExecutionState::new()
        .with_memory(memory.store(pointer, int32(9)))
        .with_resource_context(resources);
    let theorem =
        prove_symbolic_program_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("in-range block store/load should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramStatementExecutes {
            state: Box::new(state),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(9).into(),
                state: Box::new(final_state),
            },
        }
    );
}

#[test]
fn block_backed_missing_load_returns_symbolic_value_without_obligation() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let memory = Memory::new().with_block("block", 16);
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(pointer.clone()))
        .with_memory(memory.clone())
        .with_resource_context(view_memory_context(pointer.clone(), 0, 1));
    let statement = program_return(crate::kernel::program_expression::load(
        crate::kernel::program_expression::variable("p"),
    ));
    let theorem =
        prove_symbolic_program_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("in-range missing load should produce symbolic value");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramStatementExecutes {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(crate::kernel::canonical_term(&MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(memory),
                    Box::new(pointer),
                    crate::kernel::LoadKind::Int32
                )))
                .into(),
                state: Box::new(state),
            },
        }
    );
}

#[test]
fn pointer_addition_scales_int32_offsets_for_loads() {
    let base = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let second = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let memory = Memory::new()
        .with_block("block", 16)
        .store(second.clone(), int32(23));
    let resources = view_memory_context(base.clone(), 1, 2);
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(base.clone()))
        .with_memory(memory)
        .with_resource_context(resources.clone());
    let statement = program_return(crate::kernel::program_expression::load(
        crate::kernel::program_expression::add(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(1),
        ),
    ));
    let theorem =
        prove_symbolic_program_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("pointer arithmetic load should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramStatementExecutes {
            state: Box::new(state),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(23).into(),
                state: Box::new(
                    ExecutionState::new()
                        .with_local(
                            "p",
                            ProgramValue::pointer(Pointer {
                                block: "block".into(),
                                offset: PointerOffsetTerm::Constant(0),
                            }),
                        )
                        .with_memory(
                            Memory::new()
                                .with_block("block", 16)
                                .store(second, int32(23),),
                        )
                        .with_resource_context(resources)
                ),
            },
        }
    );
}

#[test]
fn pointer_addition_rejects_an_int32_index_beyond_the_object() {
    let base = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(base))
        .with_memory(Memory::new().with_block("array", 8));
    let expression = crate::kernel::program_expression::add(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(3),
    );

    let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
        .expect("concrete out-of-object pointer arithmetic should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::PointerArithmetic),
        }
    );
}

#[test]
fn uint64_pointer_index_bounds_use_the_full_value() {
    let index = MachineTerm::Variable(Variable(93_815));
    let offset = PointerOffsetTerm::scaled_int64_node(index.clone(), 1, true);
    assert_eq!(byte_offset_from_pointer_offset(&offset), None);

    let base = Pointer {
        block: "bytes".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut state = ExecutionState::new()
        .with_local("array", ProgramValue::pointer(base.clone()))
        .with_local("index", ProgramValue::UInt64(index.clone()))
        .with_memory(Memory::new().with_block("bytes", 8));
    state.locals.set_typed(
        "array",
        ProgramValue::pointer(base),
        ProgramType::UInt8Pointer,
    );
    state.locals.set_typed(
        "index",
        ProgramValue::UInt64(index.clone()),
        ProgramType::UInt64,
    );
    let expression = crate::kernel::program_expression::add(
        crate::kernel::program_expression::variable("array"),
        crate::kernel::program_expression::variable("index"),
    );
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::uint64_equal(index, MachineTerm::uint64_constant(0x1_0000_0003)),
        true,
    );
    let mut budget = ExecutionBudget::for_program_expression(&expression);
    let paths = evaluate_program_expression_paths(&state, &expression, &assumptions, &mut budget)
        .expect("wide pointer arithmetic should stay within its execution budget");

    assert!(paths.iter().any(|path| matches!(
        path.outcome,
        ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::PointerArithmetic)
    )));
    assert!(
        !paths
            .iter()
            .any(|path| matches!(path.outcome, ExpressionOutcome::Value(_)))
    );
}

#[test]
fn pointer_index_sum_overflow_is_pointer_undefined_behavior() {
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new().with_local("p", ProgramValue::pointer(base));
    let expression = crate::kernel::program_expression::add(
        crate::kernel::program_expression::add(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(i32::MAX as u32),
        ),
        crate::kernel::program_expression::int32_literal(1),
    );

    let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
        .expect("concrete cumulative pointer arithmetic should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::PointerArithmetic),
        }
    );
}

#[test]
fn pointer_index_sum_overflow_is_undefined_for_a_uint8_pointer() {
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut state = ExecutionState::new().with_local("p", ProgramValue::pointer(base.clone()));
    state
        .locals
        .set_typed("p", ProgramValue::pointer(base), ProgramType::UInt8Pointer);
    let expression = crate::kernel::program_expression::add(
        crate::kernel::program_expression::add(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(i32::MAX as u32),
        ),
        crate::kernel::program_expression::int32_literal(1),
    );

    let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
        .expect("concrete uint8 cumulative pointer arithmetic should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::PointerArithmetic,),
        }
    );
}

#[test]
fn pointer_addition_allows_the_one_past_int32_element() {
    let base = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(base.clone()))
        .with_memory(Memory::new().with_block("array", 8));
    let expression = crate::kernel::program_expression::add(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(2),
    );
    let result = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(8),
    };

    let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
        .expect("one-past pointer arithmetic should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: ExpressionOutcome::Value(ProgramValue::pointer(result)),
        }
    );
}

#[test]
fn pointer_addition_rejects_a_uint8_index_beyond_the_object() {
    let base = Pointer {
        block: "bytes".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(base.clone()))
        .with_memory(Memory::new().with_block("bytes", 4));
    state
        .locals
        .set_typed("p", ProgramValue::pointer(base), ProgramType::UInt8Pointer);
    let expression = crate::kernel::program_expression::add(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(5),
    );

    let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
        .expect("concrete uint8 out-of-object pointer arithmetic should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::PointerArithmetic,),
        }
    );
}

#[test]
fn byte_offset_rejects_a_pointer_beyond_the_object() {
    let base = Pointer {
        block: "object".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(base))
        .with_memory(Memory::new().with_block("object", 4));
    let expression = crate::kernel::program_expression::pointer_offset_bytes(
        crate::kernel::program_expression::variable("p"),
        5,
    );

    let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
        .expect("concrete out-of-object byte offset should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::PointerArithmetic,),
        }
    );
}

#[test]
fn pointer_relational_comparison_orders_same_block_elements() {
    let first = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let second = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let state = ExecutionState::new()
        .with_local("first", ProgramValue::pointer(first))
        .with_local("second", ProgramValue::pointer(second));
    let examples = [
        (
            crate::kernel::program_expression::less_than(
                crate::kernel::program_expression::variable("first"),
                crate::kernel::program_expression::variable("second"),
            ),
            1,
        ),
        (
            crate::kernel::program_expression::less_equal(
                crate::kernel::program_expression::variable("first"),
                crate::kernel::program_expression::variable("second"),
            ),
            1,
        ),
        (
            crate::kernel::program_expression::greater_than(
                crate::kernel::program_expression::variable("second"),
                crate::kernel::program_expression::variable("first"),
            ),
            1,
        ),
        (
            crate::kernel::program_expression::greater_equal(
                crate::kernel::program_expression::variable("second"),
                crate::kernel::program_expression::variable("first"),
            ),
            1,
        ),
    ];

    for (expression, expected) in examples {
        let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
            .expect("same-block pointer comparison should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::ProgramExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: ExpressionOutcome::Value(int32(expected)),
            }
        );
    }
}

#[test]
fn pointer_subtraction_returns_same_block_element_distance() {
    let start = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let end = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let state = ExecutionState::new()
        .with_local("start", ProgramValue::pointer(start))
        .with_local("end", ProgramValue::pointer(end));
    let expression = crate::kernel::program_expression::subtract(
        crate::kernel::program_expression::variable("end"),
        crate::kernel::program_expression::variable("start"),
    );

    let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
        .expect("same-block pointer subtraction should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: ExpressionOutcome::Value(int32(2)),
        }
    );
}

#[test]
fn uint8_pointer_subtraction_returns_byte_distance() {
    let start = Pointer {
        block: "bytes".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let end = Pointer {
        block: "bytes".into(),
        offset: PointerOffsetTerm::Constant(3),
    };
    let mut state = ExecutionState::new()
        .with_local("start", ProgramValue::pointer(start.clone()))
        .with_local("end", ProgramValue::pointer(end.clone()));
    state.locals.set_typed(
        "start",
        ProgramValue::pointer(start),
        ProgramType::UInt8Pointer,
    );
    state
        .locals
        .set_typed("end", ProgramValue::pointer(end), ProgramType::UInt8Pointer);
    let expression = crate::kernel::program_expression::subtract(
        crate::kernel::program_expression::variable("end"),
        crate::kernel::program_expression::variable("start"),
    );

    let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
        .expect("same-block uint8 pointer subtraction should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: ExpressionOutcome::Value(int32(3)),
        }
    );
}

#[test]
fn pointer_subtraction_by_one_steps_back_one_element() {
    let pointer = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(pointer))
        .with_memory(Memory::new().with_block("array", 12));
    let expression = crate::kernel::program_expression::subtract(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(1),
    );
    let result = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(4),
    };

    let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
        .expect("pointer subtraction by one should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: ExpressionOutcome::Value(ProgramValue::pointer(result)),
        }
    );
}

#[test]
fn pointer_comparison_rejects_different_blocks_as_undefined_behavior() {
    let left = Pointer {
        block: "left".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right = Pointer {
        block: "right".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new()
        .with_local("left", ProgramValue::pointer(left))
        .with_local("right", ProgramValue::pointer(right));
    let expression = crate::kernel::program_expression::less_than(
        crate::kernel::program_expression::variable("left"),
        crate::kernel::program_expression::variable("right"),
    );

    let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
        .expect("cross-block pointer comparison should evaluate to UB");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::PointerArithmetic),
        }
    );
}

#[test]
fn pointer_subtraction_rejects_different_blocks_as_undefined_behavior() {
    let left = Pointer {
        block: "left".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right = Pointer {
        block: "right".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new()
        .with_local("left", ProgramValue::pointer(left))
        .with_local("right", ProgramValue::pointer(right));
    let expression = crate::kernel::program_expression::subtract(
        crate::kernel::program_expression::variable("left"),
        crate::kernel::program_expression::variable("right"),
    );

    let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
        .expect("cross-block pointer subtraction should evaluate to UB");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramExpressionEvaluates {
            state: Box::new(state),
            expression,
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::PointerArithmetic),
        }
    );
}

#[test]
fn pointer_order_and_subtraction_require_external_parameters_to_share_an_object() {
    let external = |variable| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(variable)), 4),
    };
    let left = external(31_000);
    let right = external(31_001);
    let state = ExecutionState::new()
        .with_local("left", ProgramValue::pointer(left))
        .with_local("right", ProgramValue::pointer(right));

    for expression in [
        crate::kernel::program_expression::less_than(
            crate::kernel::program_expression::variable("left"),
            crate::kernel::program_expression::variable("right"),
        ),
        crate::kernel::program_expression::less_equal(
            crate::kernel::program_expression::variable("left"),
            crate::kernel::program_expression::variable("right"),
        ),
        crate::kernel::program_expression::greater_than(
            crate::kernel::program_expression::variable("left"),
            crate::kernel::program_expression::variable("right"),
        ),
        crate::kernel::program_expression::greater_equal(
            crate::kernel::program_expression::variable("left"),
            crate::kernel::program_expression::variable("right"),
        ),
        crate::kernel::program_expression::subtract(
            crate::kernel::program_expression::variable("left"),
            crate::kernel::program_expression::variable("right"),
        ),
    ] {
        let mut budget = ExecutionBudget::for_program_expression(&expression);
        let paths = evaluate_program_expression_paths(
            &state,
            &expression,
            &PureFactContext::new(),
            &mut budget,
        )
        .expect("external pointer operation should stay within its execution budget");
        assert!(
            paths
                .iter()
                .any(|path| matches!(path.outcome, ExpressionOutcome::Value(_)))
        );
        assert!(paths.iter().any(|path| matches!(
            path.outcome,
            ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::PointerArithmetic)
        )));
    }

    for expression in [
        crate::kernel::program_expression::equal(
            crate::kernel::program_expression::variable("left"),
            crate::kernel::program_expression::variable("right"),
        ),
        crate::kernel::program_expression::not_equal(
            crate::kernel::program_expression::variable("left"),
            crate::kernel::program_expression::variable("right"),
        ),
    ] {
        let mut budget = ExecutionBudget::for_program_expression(&expression);
        let paths = evaluate_program_expression_paths(
            &state,
            &expression,
            &PureFactContext::new(),
            &mut budget,
        )
        .expect("external pointer equality should stay within its execution budget");
        assert!(!paths.is_empty());
        assert!(
            paths
                .iter()
                .all(|path| matches!(path.outcome, ExpressionOutcome::Value(_)))
        );
    }
}

#[test]
fn null_pointers_have_no_object_provenance_for_ordering_or_subtraction() {
    let null = Pointer::null();
    assert!(disprove_builtin_prop(&pointer_same_object_proposition(
        &null, &null
    )));

    let state = ExecutionState::new()
        .with_local("left", ProgramValue::pointer(null.clone()))
        .with_local("right", ProgramValue::pointer(null));
    for expression in [
        crate::kernel::program_expression::less_than(
            crate::kernel::program_expression::variable("left"),
            crate::kernel::program_expression::variable("right"),
        ),
        crate::kernel::program_expression::less_equal(
            crate::kernel::program_expression::variable("left"),
            crate::kernel::program_expression::variable("right"),
        ),
        crate::kernel::program_expression::greater_than(
            crate::kernel::program_expression::variable("left"),
            crate::kernel::program_expression::variable("right"),
        ),
        crate::kernel::program_expression::greater_equal(
            crate::kernel::program_expression::variable("left"),
            crate::kernel::program_expression::variable("right"),
        ),
        crate::kernel::program_expression::subtract(
            crate::kernel::program_expression::variable("left"),
            crate::kernel::program_expression::variable("right"),
        ),
    ] {
        let theorem = prove_program_expression_evaluation(state.clone(), expression.clone())
            .expect("a null pointer operation should evaluate to undefined behavior");
        assert_eq!(
            theorem.proposition(),
            &Proposition::ProgramExpressionEvaluates {
                state: Box::new(state.clone()),
                expression,
                outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::PointerArithmetic,),
            }
        );
    }

    for expression in [
        crate::kernel::program_expression::equal(
            crate::kernel::program_expression::variable("left"),
            crate::kernel::program_expression::variable("right"),
        ),
        crate::kernel::program_expression::not_equal(
            crate::kernel::program_expression::variable("left"),
            crate::kernel::program_expression::variable("right"),
        ),
    ] {
        let mut budget = ExecutionBudget::for_program_expression(&expression);
        let paths = evaluate_program_expression_paths(
            &state,
            &expression,
            &PureFactContext::new(),
            &mut budget,
        )
        .expect("null pointer equality should stay within its execution budget");
        assert!(!paths.is_empty());
        assert!(
            paths
                .iter()
                .all(|path| matches!(path.outcome, ExpressionOutcome::Value(_)))
        );
    }
}

#[test]
fn an_external_pointer_does_not_share_an_object_with_itself_until_nonnull() {
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(31_050)), 4),
    };
    let state = ExecutionState::new().with_local("pointer", ProgramValue::pointer(pointer));

    for expression in [
        crate::kernel::program_expression::less_than(
            crate::kernel::program_expression::variable("pointer"),
            crate::kernel::program_expression::variable("pointer"),
        ),
        crate::kernel::program_expression::less_equal(
            crate::kernel::program_expression::variable("pointer"),
            crate::kernel::program_expression::variable("pointer"),
        ),
        crate::kernel::program_expression::greater_than(
            crate::kernel::program_expression::variable("pointer"),
            crate::kernel::program_expression::variable("pointer"),
        ),
        crate::kernel::program_expression::greater_equal(
            crate::kernel::program_expression::variable("pointer"),
            crate::kernel::program_expression::variable("pointer"),
        ),
        crate::kernel::program_expression::subtract(
            crate::kernel::program_expression::variable("pointer"),
            crate::kernel::program_expression::variable("pointer"),
        ),
    ] {
        let mut budget = ExecutionBudget::for_program_expression(&expression);
        let paths = evaluate_program_expression_paths(
            &state,
            &expression,
            &PureFactContext::new(),
            &mut budget,
        )
        .expect("external pointer operation should stay within its execution budget");
        assert!(
            paths
                .iter()
                .any(|path| matches!(path.outcome, ExpressionOutcome::Value(_)))
        );
        assert!(paths.iter().any(|path| matches!(
            path.outcome,
            ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::PointerArithmetic)
        )));
    }
}

#[test]
fn nonempty_loadability_establishes_external_pointer_object_provenance() {
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(31_060)), 4),
    };
    let state = ExecutionState::new().with_local("pointer", ProgramValue::pointer(pointer.clone()));
    let loadable = |bytes| Proposition::MemoryLoadable {
        memory: state.memory().clone(),
        base: pointer.clone(),
        bytes: MachineTerm::constant(bytes),
        wide: false,
    };

    let nonempty = PureFactContext::new().assume_proposition(loadable(4));
    for expression in [
        crate::kernel::program_expression::less_equal(
            crate::kernel::program_expression::variable("pointer"),
            crate::kernel::program_expression::variable("pointer"),
        ),
        crate::kernel::program_expression::subtract(
            crate::kernel::program_expression::variable("pointer"),
            crate::kernel::program_expression::variable("pointer"),
        ),
    ] {
        let mut budget = ExecutionBudget::for_program_expression(&expression);
        let paths = evaluate_program_expression_paths(&state, &expression, &nonempty, &mut budget)
            .expect("viewable pointer operation should stay within its execution budget");
        assert!(!paths.is_empty());
        assert!(
            paths
                .iter()
                .all(|path| matches!(path.outcome, ExpressionOutcome::Value(_)))
        );
    }

    let empty = PureFactContext::new().assume_proposition(loadable(0));
    let expression = crate::kernel::program_expression::less_equal(
        crate::kernel::program_expression::variable("pointer"),
        crate::kernel::program_expression::variable("pointer"),
    );
    let mut budget = ExecutionBudget::for_program_expression(&expression);
    let paths = evaluate_program_expression_paths(&state, &expression, &empty, &mut budget)
        .expect("empty-viewable pointer operation should stay within its execution budget");
    assert!(paths.iter().any(|path| matches!(
        path.outcome,
        ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::PointerArithmetic)
    )));
}

#[test]
fn pointer_arithmetic_preserves_external_object_identity() {
    let left = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(31_100)), 4),
    };
    let right = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(31_101)), 4),
    };
    let derived_left = left.offset_by_int32_elements(MachineTerm::Variable(Variable(31_102)));
    let derived_right = right.offset_by_int32_elements(MachineTerm::constant(1));

    assert_eq!(
        pointer_object_identity_condition(&derived_left, &derived_right),
        pointer_object_identity_condition(&left, &right)
    );

    let raw_address_equality = pointer_equality_condition(left.clone(), right.clone());
    let equal_addresses = PureFactContext::new().assume_condition(raw_address_equality, true);
    assert_eq!(
        equal_addresses.decide(&pointer_object_identity_condition(&left, &right)),
        None,
        "address equality must not imply same-object provenance"
    );
}

#[test]
fn viewed_memory_resource_permits_pointer_addition_load_beyond_memory_block() {
    let base = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let derived = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let memory = Memory::new().with_block("block", 4);
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(base.clone()))
        .with_memory(memory.clone())
        .with_resource_context(view_memory_context(base, 1, 2));
    let statement = program_return(crate::kernel::program_expression::load(
        crate::kernel::program_expression::add(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(1),
        ),
    ));
    let execution = prove_symbolic_program_execution_paths(
        state.clone(),
        statement.clone(),
        PureFactContext::new(),
    );

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(execution.paths()[0].obligations(), &[]);
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::ProgramStatementExecutes {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(crate::kernel::canonical_term(&MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(memory),
                    Box::new(derived),
                    crate::kernel::LoadKind::Int32,
                )))
                .into(),
                state: Box::new(state),
            },
        }
    );
}

#[test]
fn fixed_bound_store_loop_touches_only_valid_pointer_range() {
    let base = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = Memory::new().with_block("block", 12);
    let resources = own_memory_context(base.clone(), 0, 3);
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(base.clone()))
        .with_local("i", int32(0))
        .with_memory(memory.clone())
        .with_resource_context(resources.clone());
    let loop_statement = program_while(
        crate::kernel::program_expression::less_than(
            crate::kernel::program_expression::variable("i"),
            crate::kernel::program_expression::int32_literal(3),
        ),
        Vec::new(),
        program_seq(
            program_store(
                crate::kernel::program_expression::add(
                    crate::kernel::program_expression::variable("p"),
                    crate::kernel::program_expression::variable("i"),
                ),
                crate::kernel::program_expression::variable("i"),
            ),
            program_assign(
                "i",
                crate::kernel::program_expression::add(
                    crate::kernel::program_expression::variable("i"),
                    crate::kernel::program_expression::int32_literal(1),
                ),
            ),
        ),
    );
    let statement = program_seq(
        loop_statement,
        program_return(crate::kernel::program_expression::variable("i")),
    );
    let final_memory = memory
        .store(
            Pointer {
                block: "block".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            int32(0),
        )
        .store(
            Pointer {
                block: "block".into(),
                offset: PointerOffsetTerm::Constant(4),
            },
            int32(1),
        )
        .store(
            Pointer {
                block: "block".into(),
                offset: PointerOffsetTerm::Constant(8),
            },
            int32(2),
        );
    let final_state = ExecutionState::new()
        .with_local(
            "p",
            ProgramValue::pointer(Pointer {
                block: "block".into(),
                offset: PointerOffsetTerm::Constant(0),
            }),
        )
        .with_local("i", int32(3))
        .with_memory(final_memory)
        .with_resource_context(resources);
    let execution = prove_symbolic_program_execution_paths(
        state.clone(),
        statement.clone(),
        PureFactContext::new(),
    );

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::ProgramStatementExecutes {
            state: Box::new(state),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(3).into(),
                state: Box::new(final_state),
            },
        }
    );
}

#[test]
fn symbolic_loadable_discharges_pointer_access_obligation() {
    let i = Variable(67);
    let n = Variable(68);
    let i_bits = MachineTerm::Variable(i);
    let n_bits = MachineTerm::Variable(n);
    let memory = Memory::new();
    let base = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(base.clone()))
        .with_local("i", int32(i_bits.clone()))
        .with_memory(memory.clone())
        .with_resource_context(own_memory_context(base.clone(), 0, n_bits.clone()));
    let statement = program_store(
        crate::kernel::program_expression::add(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::variable("i"),
        ),
        crate::kernel::program_expression::int32_literal(7),
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: binary_node!(
                Int32,
                Multiply,
                Box::new(n_bits.clone()),
                Box::new(MachineTerm::constant(4)),
            ),
            wide: false,
        })
        .assume_condition(
            ConditionTerm::signed_greater_equal(i_bits.clone(), MachineTerm::constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(i_bits.clone(), n_bits),
            true,
        );
    let execution = prove_symbolic_program_execution_paths(state, statement, assumptions);

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
}

#[test]
fn signed_order_solver_knows_int32_universal_bounds() {
    let x = MachineTerm::Variable(Variable(71));
    let int_min = MachineTerm::constant(i32::MIN as u32);
    let int_max = MachineTerm::constant(i32::MAX as u32);
    let assumptions = PureFactContext::new();

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_equal(
            x.clone(),
            int_max.clone()
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_than(x.clone(), int_max)),
        Some(false)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_equal(
            x.clone(),
            int_min.clone()
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(x, int_min)),
        Some(false)
    );
}

#[test]
fn strict_positive_bound_rules_out_decrement_overflow() {
    let value = MachineTerm::Variable(Variable(72_001));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_than(MachineTerm::constant(1), value.clone()),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_subtract_overflows(
            value,
            MachineTerm::constant(1),
        )),
        Some(false)
    );
}

#[test]
fn nonnegative_bound_rules_out_decrement_overflow() {
    let value = MachineTerm::Variable(Variable(72_002));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_greater_equal(value.clone(), MachineTerm::constant(0)),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_subtract_overflows(
            value,
            MachineTerm::constant(1),
        )),
        Some(false)
    );
}

#[test]
fn interval_arithmetic_uses_lower_bound_for_incremented_values() {
    let i = Variable(73);
    let i_bits = MachineTerm::Variable(i);
    let incremented = binary_node!(
        Int32,
        Add,
        Box::new(i_bits.clone()),
        Box::new(MachineTerm::constant(1)),
    );
    // A lower bound alone is not enough: `i + 1` wraps at INT_MAX, so
    // `i >= 1` does not entail `i + 1 >= 1` (false at i = INT_MAX).
    let lower_only = PureFactContext::new().assume_condition(
        ConditionTerm::signed_greater_equal(i_bits.clone(), MachineTerm::constant(1)),
        true,
    );
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(lower_only),
        &Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(incremented.clone(), MachineTerm::constant(1),),
            true,
        )
    ));

    // Knowing `i < INT_MAX` rules out signed overflow of `i + 1`, so the
    // lower bound carries to the incremented value.
    let assumptions = lower_only.assume_condition(
        ConditionTerm::signed_less_than(i_bits, MachineTerm::constant(i32::MAX as u32)),
        true,
    );
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(incremented.clone(), MachineTerm::constant(1),),
            true,
        )
    ));
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(
            ConditionTerm::signed_greater_than(incremented, MachineTerm::constant(0)),
            true,
        )
    ));
}

#[test]
fn nonnegative_successor_requires_no_overflow_evidence() {
    let x = MachineTerm::Variable(Variable(74_001));
    let successor = MachineTerm::add(x.clone(), MachineTerm::constant(1));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_greater_equal(x.clone(), MachineTerm::constant(0)),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_equal(
            successor.clone(),
            MachineTerm::constant(0),
        )),
        None,
    );
    assert!(
        crate::kernel::search::ProofSearch::derive_solve_proposition(
            &(assumptions),
            &Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(successor, MachineTerm::constant(0),),
                true,
            )
        )
        .is_none()
    );
}

#[test]
fn additive_upper_bound_covers_incremented_pointer_access() {
    let j = Variable(74);
    let j_bits = MachineTerm::Variable(j);
    let incremented = MachineTerm::add(j_bits.clone(), MachineTerm::constant(1));
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let pointer = base.offset_by_int32_elements(incremented.clone());
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(j_bits.clone(), MachineTerm::constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j_bits, MachineTerm::constant(2)),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            incremented,
            MachineTerm::constant(3),
        )),
        Some(true)
    );
    assert!(assumptions.pointer_access_in_range(
        &pointer,
        4,
        &base,
        &MachineTerm::constant(0),
        &MachineTerm::constant(3),
        4,
    ));
}

#[test]
fn relative_dependent_range_is_covered_by_owned_range() {
    let owner = MachineTerm::Variable(Variable(75));
    let backing = MachineTerm::Variable(Variable(76));
    let index = MachineTerm::Variable(Variable(77));
    let length = MachineTerm::Variable(Variable(78));
    let capacity = MachineTerm::Variable(Variable(79));
    let base = Pointer {
        block: "owner".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let backing_start = MachineTerm::subtract(backing.clone(), owner.clone());
    let indexed_start = MachineTerm::subtract(MachineTerm::add(backing, index.clone()), owner);
    let available = ResourceFact::own_memory(MemoryRange::new(
        base.clone(),
        backing_start.clone(),
        MachineTerm::add(backing_start, capacity.clone()),
    ));
    let required = ResourceFact::own_memory(MemoryRange::new(
        base,
        indexed_start.clone(),
        MachineTerm::add(indexed_start, MachineTerm::constant(1)),
    ));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(index.clone(), MachineTerm::constant(0)),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(index, length.clone()), true)
        .assume_condition(ConditionTerm::signed_less_equal(length, capacity), true);
    // Publish the symbolic supplier at construction, before containment queries.
    let resources =
        ResourceContext::new_with_equalities(&assumptions).unchecked_with_fact(available);

    assert!(resources.satisfies_fact(&required, &assumptions));
    assert!(resources.without_fact(&required, &assumptions).is_some());
}

#[test]
fn addition_cancels_a_negated_pointer_base() {
    let base = MachineTerm::Variable(Variable(90));
    let index = MachineTerm::Variable(Variable(91));
    let negative_base = MachineTerm::subtract(MachineTerm::constant(0), base.clone());

    assert_eq!(
        MachineTerm::add(negative_base, MachineTerm::add(base, index.clone()),),
        index
    );
}

#[test]
fn negative_equality_fact_decides_equality_false() {
    let x = MachineTerm::Variable(Variable(79));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::equal(x.clone(), MachineTerm::constant(0)),
        false,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::equal(MachineTerm::constant(0), x,)),
        Some(false)
    );
}

#[test]
fn equality_facts_are_transitive() {
    let i = MachineTerm::Variable(Variable(84));
    let k = MachineTerm::Variable(Variable(85));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(k.clone(), i.clone()), true)
        .assume_condition(ConditionTerm::equal(i, MachineTerm::constant(1)), true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::equal(k, MachineTerm::constant(1))),
        Some(true)
    );
}

#[test]
fn equality_transports_signed_order_facts_in_both_directions() {
    let selected = MachineTerm::Variable(Variable(86));
    let key = MachineTerm::Variable(Variable(87));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(selected.clone(), key.clone()), true)
        .assume_condition(
            ConditionTerm::signed_greater_equal(key.clone(), MachineTerm::constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(10), selected.clone()),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_equal(
            selected,
            MachineTerm::constant(0),
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_equal(
            MachineTerm::constant(10),
            key,
        )),
        Some(true)
    );
}

#[test]
fn solve_combines_equality_with_discrete_integer_bounds() {
    let length = MachineTerm::Variable(Variable(87_100));
    let owner_length = MachineTerm::Variable(Variable(87_101));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(2), length.clone()),
            true,
        )
        .assume_condition(ConditionTerm::equal(owner_length.clone(), length), true);

    assert_eq!(
        assumptions.selected_for_test().decide_selected_condition(
            &ConditionTerm::signed_less_than(MachineTerm::constant(1), owner_length,)
        ),
        Some(true)
    );
}

#[test]
fn solve_evaluates_equality_arithmetic_chains() {
    let old_split = MachineTerm::Variable(Variable(87_102));
    let split = MachineTerm::Variable(Variable(87_103));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(old_split.clone(), MachineTerm::constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(
                split.clone(),
                MachineTerm::add(old_split, MachineTerm::constant(1)),
            ),
            true,
        );

    assert_eq!(
        assumptions.selected_for_test().decide_selected_condition(
            &ConditionTerm::signed_less_than(MachineTerm::constant(1), split,)
        ),
        Some(true)
    );
}

#[test]
fn equality_transport_reaches_chains_and_arithmetic_terms() {
    let x = MachineTerm::Variable(Variable(88));
    let y = MachineTerm::Variable(Variable(89));
    let z = MachineTerm::Variable(Variable(90));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(x.clone(), y), true)
        .assume_condition(ConditionTerm::equal(z.clone(), x), true)
        .assume_condition(
            ConditionTerm::signed_less_than(
                MachineTerm::add(z, MachineTerm::constant(1)),
                MachineTerm::constant(8),
            ),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            MachineTerm::add(
                MachineTerm::Variable(Variable(89)),
                MachineTerm::constant(1),
            ),
            MachineTerm::constant(8),
        )),
        Some(true)
    );
}

#[test]
fn excluded_small_integer_range_is_inconsistent() {
    let k = MachineTerm::Variable(Variable(80));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), k.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(k.clone(), MachineTerm::constant(3)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(k.clone(), MachineTerm::constant(0)),
            false,
        )
        .assume_condition(
            ConditionTerm::equal(k.clone(), MachineTerm::constant(1)),
            false,
        )
        .assume_condition(ConditionTerm::equal(k, MachineTerm::constant(2)), false);

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &false_equals_true_proposition()
    ));
}

#[test]
fn excluded_range_endpoints_force_the_remaining_value() {
    // `0 <= k < 4` with `k != 0`, `k != 1` and `k != 3` leaves only `k == 2`;
    // without the exclusion at either end the value stays undecided.
    let k = MachineTerm::Variable(Variable(87));
    let bounded = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), k.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(k.clone(), MachineTerm::constant(4)),
            true,
        );
    let exclude = |assumptions: PureFactContext, value: u32| {
        assumptions.assume_condition(
            ConditionTerm::equal(k.clone(), MachineTerm::constant(value)),
            false,
        )
    };
    let is_two = ConditionTerm::equal(k.clone(), MachineTerm::constant(2));
    let all = exclude(exclude(exclude(bounded.clone(), 0), 1), 3);
    assert_eq!(all.decide(&is_two), Some(true));
    let low_only = exclude(exclude(bounded.clone(), 0), 1);
    assert_eq!(low_only.decide(&is_two), None);
    let high_only = exclude(exclude(bounded, 1), 3);
    assert_eq!(high_only.decide(&is_two), None);
}

#[test]
fn a_signed_interval_moves_past_excluded_endpoints() {
    let k = MachineTerm::Variable(Variable(88));
    let assumptions = [1, 2, 3, 5].into_iter().fold(
        PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(MachineTerm::constant(0), k.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(k.clone(), MachineTerm::constant(4)),
                true,
            ),
        |assumptions, value| {
            assumptions.assume_condition(
                ConditionTerm::equal(k.clone(), MachineTerm::constant(value)),
                false,
            )
        },
    );
    assert_eq!(assumptions.signed_interval(&k), Some((0, 3)));
    // `k != 5` lies outside the range and moves nothing.
    assert_eq!(
        assumptions.signed_interval_past_exclusions(&k),
        Some((0, 0))
    );
}

#[test]
fn singleton_integer_range_forces_equality() {
    let k = MachineTerm::Variable(Variable(86));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), k.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(k.clone(), MachineTerm::constant(1)),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::equal(k, MachineTerm::constant(0))),
        Some(true)
    );
}

#[test]
fn signed_byte_narrowing_checks_each_bound_and_unsigned_inputs() {
    use crate::kernel::eval::IntegerConversion;
    let convert = |value: ProgramValue,
                   conversion,
                   obligations: &mut Vec<ProofObligation>,
                   assumptions: &PureFactContext| {
        crate::kernel::eval::coerce_program_value_to_type_as(
            value,
            ProgramType::Int8,
            conversion,
            obligations,
            assumptions,
        )
    };
    for (input, valid) in [
        (int32((-129i32) as u32), false),
        (int32((-128i32) as u32), true),
        (int32(127), true),
        (int32(128), false),
        (int16((-129i32) as u32), false),
        (int16((-128i32) as u32), true),
        (uint8(127), true),
        (uint8(128), false),
        (uint8(255), false),
    ] {
        let mut obligations = Vec::new();
        // C's conversion is the low byte, read as signed, owing nothing.
        let word = match &input {
            ProgramValue::Int32(int32_constant!(word)) => constant_u32(*word),
            narrow @ (ProgramValue::Int16(_) | ProgramValue::UInt8(_)) => {
                MachineIntegerType::from_program_type(narrow.program_type())
                    .and_then(|ty| ty.constant_from_value(narrow))
                    .and_then(|value| value.to_i128())
                    .expect("a narrow constant") as i32 as u32
            }
            other => panic!("{other:?}"),
        };
        assert_eq!(
            convert(
                input.clone(),
                IntegerConversion::Modular,
                &mut obligations,
                &PureFactContext::new()
            ),
            Some(int8(i32::from(word as u8 as i8) as u32)),
            "{input:?}"
        );
        assert!(obligations.is_empty());
        let result = convert(
            input.clone(),
            IntegerConversion::Checked,
            &mut obligations,
            &PureFactContext::new(),
        );
        assert_eq!(
            result.unwrap().program_type(),
            ProgramType::Int8,
            "{input:?}"
        );
        assert_eq!(obligations.is_empty(), valid, "{input:?}");
        for obligation in &obligations {
            let Proposition::ConditionIs(condition, true) = obligation.proposition() else {
                panic!("narrowing owes an explicit range comparison");
            };
            assert_eq!(
                PureFactContext::decide_intrinsically(condition),
                Some(false)
            );
            assert!(obligation.context().unwrap().starts_with("int8 narrowing"));
        }
    }
    let value = MachineTerm::Variable(Variable(815));
    let bounds = [
        ConditionTerm::signed_greater_equal(value.clone(), MachineTerm::constant((-128i32) as u32)),
        ConditionTerm::signed_less_equal(value.clone(), MachineTerm::constant(127)),
    ];
    for mask in 0u32..4 {
        let mut assumptions = PureFactContext::new();
        for (index, bound) in bounds.iter().enumerate() {
            if mask & (1 << index) != 0 {
                assumptions = assumptions.assume_condition(bound.clone(), true);
            }
        }
        let mut obligations = Vec::new();
        let result = convert(
            int32(value.clone()),
            IntegerConversion::Checked,
            &mut obligations,
            &assumptions,
        );
        // A checked narrowing is the typed conversion node too, the
        // destination's canonical carrier. Its identity with the operand,
        // which holds exactly where the obligations do, is the fact the cast
        // files beside them.
        let checked = int8(MachineTerm::machine_integer_cast(
            crate::kernel::MachineIntegerType::Int32,
            crate::kernel::MachineIntegerType::Int8,
            value.clone(),
        ));
        assert_eq!(result, Some(checked.clone()));
        assert_eq!(obligations.len(), 2 - mask.count_ones() as usize);
        // It is filed as values and as the 32-bit word comparison of the
        // narrow value's widening with the operand.
        assert_eq!(
            crate::kernel::eval::checked_narrowing_identity(&int32(value.clone()), &checked),
            vec![
                Proposition::ConditionIs(
                    ConditionTerm::integer_equal(
                        IntegerTerm::from_machine(
                            crate::kernel::MachineIntegerType::Int8,
                            checked_term(&checked),
                        )
                        .unwrap(),
                        IntegerTerm::from_machine(
                            crate::kernel::MachineIntegerType::Int32,
                            value.clone(),
                        )
                        .unwrap(),
                    ),
                    true,
                ),
                Proposition::ConditionIs(
                    ConditionTerm::equal(
                        MachineTerm::machine_integer_cast(
                            crate::kernel::MachineIntegerType::Int8,
                            crate::kernel::MachineIntegerType::Int32,
                            checked_term(&checked),
                        ),
                        value.clone()
                    ),
                    true,
                ),
            ]
        );
        // C's conversion owes nothing, and its term is the typed conversion
        // node whatever the context knows; the identity inside the range is
        // reasoning (`narrowed_cast_identity`), not a choice made here.
        let mut obligations = Vec::new();
        let modular = convert(
            int32(value.clone()),
            IntegerConversion::Modular,
            &mut obligations,
            &assumptions,
        );
        assert!(obligations.is_empty());
        assert_eq!(
            modular,
            Some(int8(MachineTerm::machine_integer_cast(
                crate::kernel::MachineIntegerType::Int32,
                crate::kernel::MachineIntegerType::Int8,
                value.clone(),
            )))
        );
    }
}

#[test]
fn signed_byte_arithmetic_promotes_with_range_facts() {
    let value = ProgramExpression::Value(int8(MachineTerm::Variable(Variable(817))));
    let expression = ProgramExpression::Subtract(
        Box::new(ProgramExpression::Multiply(
            Box::new(value),
            Box::new(crate::kernel::program_expression::int32_literal(2)),
        )),
        Box::new(crate::kernel::program_expression::int32_literal(1)),
    );
    let paths = evaluate_program_expression_paths(
        &ExecutionState::new(),
        &expression,
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert_eq!(paths.len(), 1, "{paths:?}");
    assert!(
        matches!(
            paths[0].outcome,
            ExpressionOutcome::Value(ProgramValue::Int32(_))
        ),
        "{paths:?}"
    );
}

#[test]
fn exact_signed_constant_bounds_preserve_frozen_load_identity() {
    let pointer = Pointer {
        block: "bounded".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = Memory::new().with_block("bounded", 8);
    let load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(memory.clone()),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_greater_equal(load.clone(), MachineTerm::constant(2)),
        true,
    );
    assert_eq!(
        assumptions.selected_for_test().decide_selected_condition(
            &ConditionTerm::signed_greater_than(load.clone(), MachineTerm::constant(1))
        ),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_than(
            load,
            MachineTerm::constant(1)
        )),
        Some(true)
    );
    let changed = memory.clone().store(
        pointer.clone(),
        ProgramValue::Int32(MachineTerm::constant(0)),
    );
    let changed_load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(changed),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let other_load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(memory),
        Box::new(Pointer {
            block: pointer.block,
            offset: PointerOffsetTerm::Constant(4),
        }),
        crate::kernel::LoadKind::Int32,
    );
    for unrelated in [changed_load, other_load] {
        assert_ne!(
            assumptions.selected_for_test().decide_selected_condition(
                &ConditionTerm::signed_greater_than(unrelated, MachineTerm::constant(1))
            ),
            Some(true)
        );
    }
}

#[test]
fn exact_signed_constant_bounds_check_signed_endpoints() {
    let value = MachineTerm::Variable(Variable(87_900));
    let empty = PureFactContext::new();
    for (bound, greater, expected) in [(i32::MAX, true, false), (i32::MIN, false, false)] {
        let condition = if greater {
            ConditionTerm::signed_greater_than(value.clone(), MachineTerm::constant(bound as u32))
        } else {
            ConditionTerm::signed_less_than(value.clone(), MachineTerm::constant(bound as u32))
        };
        assert_eq!(
            empty
                .selected_for_test()
                .decide_selected_condition(&condition),
            Some(expected)
        );
    }
    let at_max = PureFactContext::new().assume_condition(
        ConditionTerm::signed_greater_equal(value.clone(), MachineTerm::constant(i32::MAX as u32)),
        true,
    );
    assert_eq!(
        at_max
            .selected_for_test()
            .decide_selected_condition(&ConditionTerm::signed_greater_than(
                value.clone(),
                MachineTerm::constant((i32::MAX - 1) as u32)
            )),
        Some(true)
    );
    let at_min = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_equal(value.clone(), MachineTerm::constant(i32::MIN as u32)),
        true,
    );
    assert_eq!(
        at_min
            .selected_for_test()
            .decide_selected_condition(&ConditionTerm::signed_less_than(
                value,
                MachineTerm::constant((i32::MIN + 1) as u32)
            )),
        Some(true)
    );
}

#[test]
fn exact_signed_mirror_normalization_checks_state_address_and_selected_premise() {
    let pointer = Pointer {
        block: "mirror".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = Memory::new().with_block("mirror", 8);
    let load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(memory.clone()),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(MachineTerm::constant(1), load.clone()),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(load, MachineTerm::constant(1)),
        true,
    );
    let facts = crate::kernel::proof::ProofFacts::from_ordered(std::slice::from_ref(&premise));
    assert!(
        crate::kernel::proof::fact_reasoning::normalize_using_conditions(
            &goal,
            std::slice::from_ref(&premise),
            &facts
        )
        .is_ok()
    );
    let changed = memory.clone().store(
        pointer.clone(),
        ProgramValue::Int32(MachineTerm::constant(0)),
    );
    for (retained_state, address) in [
        (changed, pointer.clone()),
        (
            memory,
            Pointer {
                block: pointer.block,
                offset: PointerOffsetTerm::Constant(4),
            },
        ),
    ] {
        let unrelated = MachineTerm::MemoryLoad(
            crate::kernel::intern_memory(retained_state),
            Box::new(address),
            crate::kernel::LoadKind::Int32,
        );
        let bad = Proposition::ConditionIs(
            ConditionTerm::signed_greater_than(unrelated, MachineTerm::constant(1)),
            true,
        );
        assert!(
            crate::kernel::proof::fact_reasoning::normalize_using_conditions(
                &bad,
                std::slice::from_ref(&premise),
                &facts
            )
            .is_err()
        );
    }
    assert!(
        crate::kernel::proof::fact_reasoning::normalize_using_conditions(
            &goal,
            &[premise],
            &crate::kernel::proof::ProofFacts::from_ordered(&[])
        )
        .is_err()
    );
}

#[test]
fn uint64_bit_reinterpretation_has_a_distinct_checked_cast_boundary() {
    let assert_type_mismatch = |expression| {
        let theorem =
            prove_program_expression_evaluation(ExecutionState::new(), expression).unwrap();
        assert!(matches!(
            theorem.proposition(),
            Proposition::ProgramExpressionEvaluates {
                outcome: ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch),
                ..
            }
        ));
    };
    for bits in [0u64, 1, i64::MAX as u64, 1u64 << 63, u64::MAX] {
        let expression = crate::kernel::program_expression::uint64_bits_to_int64(
            crate::kernel::program_expression::uint64_literal(bits),
        );
        let theorem =
            prove_program_expression_evaluation(ExecutionState::new(), expression).unwrap();
        let Proposition::ProgramExpressionEvaluates {
            outcome: ExpressionOutcome::Value(ProgramValue::Int64(value)),
            ..
        } = theorem.proposition()
        else {
            panic!("expected signed bits");
        };
        assert_eq!(value.int64_as_const(), Some(bits as i64));
        // Bit reinterpretation accepts every bit pattern. Ordinary conversion
        // preserves the value only within the signed destination's range.
        let ordinary = crate::kernel::program_expression::cast(
            crate::kernel::program_expression::uint64_literal(bits),
            ProgramType::Int64,
        );
        if bits <= i64::MAX as u64 {
            let theorem =
                prove_program_expression_evaluation(ExecutionState::new(), ordinary).unwrap();
            let Proposition::ProgramExpressionEvaluates {
                outcome: ExpressionOutcome::Value(ProgramValue::Int64(value)),
                ..
            } = theorem.proposition()
            else {
                panic!("representable ordinary cast must preserve its value");
            };
            assert_eq!(value.int64_as_const(), Some(bits as i64));
        } else {
            assert!(prove_program_expression_evaluation(ExecutionState::new(), ordinary).is_none());
        }
    }
    assert_type_mismatch(crate::kernel::program_expression::uint64_bits_to_int64(
        crate::kernel::program_expression::int32_literal(1),
    ));
    let mut malformed = crate::kernel::program_expression::uint64_bits_to_int64(
        crate::kernel::program_expression::uint64_literal(1),
    );
    let ProgramExpression::Cast { target_type, .. } = &mut malformed else {
        unreachable!()
    };
    *target_type = ProgramType::UInt64;
    assert_type_mismatch(malformed);
}

#[test]
fn reinterpreted_unsigned_arithmetic_keeps_signed_operators_and_definedness() {
    let source = MachineTerm::uint64_subtract(
        MachineTerm::Variable(Variable(139_001)),
        MachineTerm::uint64_constant(1),
    );
    let converted = MachineTerm::int64_from_uint64_bits(source.clone());
    assert_eq!(converted, source); // Preserve the symbolic 64-bit expression.
    let wrapped = MachineTerm::Binary {
        format: MachineIntegerType::UInt64,
        op: MachineBinaryOp::Add,
        left: Box::new(MachineTerm::uint64_constant(u64::MAX)),
        right: Box::new(MachineTerm::uint64_constant(1)),
    };
    assert_eq!(wrapped.int64_as_const(), Some(0));
    let high = MachineTerm::uint64_constant(1u64 << 63);
    assert_eq!(
        MachineTerm::int64_divide(high, MachineTerm::int64_constant(-1)).int64_as_const(),
        None
    );
    assert_eq!(
        MachineTerm::int64_divide(
            MachineTerm::int64_constant(1),
            MachineTerm::int64_constant(0)
        )
        .int64_as_const(),
        None
    );
}

#[test]
fn modulo_casts_are_explicit_integer_boundaries_and_preserve_operand_definedness() {
    let outcome = |expression| {
        let theorem =
            prove_program_expression_evaluation(ExecutionState::new(), expression).unwrap();
        let Proposition::ProgramExpressionEvaluates { outcome, .. } = theorem.proposition() else {
            panic!("expected evaluation");
        };
        outcome.clone()
    };
    for target in [
        ProgramType::Int8,
        ProgramType::Int16,
        ProgramType::Int32,
        ProgramType::Int64,
        ProgramType::UInt8,
        ProgramType::UInt16,
        ProgramType::UInt32,
        ProgramType::UInt64,
    ] {
        for flag in [false, true] {
            let actual = outcome(crate::kernel::program_expression::integer_cast_modulo(
                ProgramExpression::Value(ProgramValue::bool_constant(flag)),
                target,
            ));
            let ty = MachineIntegerType::from_program_type(target).unwrap();
            let expected = ty
                .constant_value(
                    MachineIntegerConstant::from_unsigned(ty.format(), u128::from(flag)).unwrap(),
                )
                .unwrap();
            assert_eq!(actual, ExpressionOutcome::Value(expected));
        }
    }
    for expression in [
        crate::kernel::program_expression::integer_cast_modulo(
            crate::kernel::program_expression::int32_literal(1),
            ProgramType::Bool,
        ),
        crate::kernel::program_expression::integer_cast_modulo(
            crate::kernel::program_expression::int32_literal(1),
            ProgramType::Float64,
        ),
        crate::kernel::program_expression::integer_cast_modulo(
            crate::kernel::program_expression::int32_literal(1),
            ProgramType::Int32Pointer,
        ),
        crate::kernel::program_expression::integer_cast_modulo(
            ProgramExpression::Value(ProgramValue::Float32(MachineTerm::constant(0))),
            ProgramType::Int32,
        ),
        crate::kernel::program_expression::integer_cast_modulo(
            ProgramExpression::Value(ProgramValue::typed_pointer(
                Pointer::null(),
                ProgramType::Int32Pointer,
            )),
            ProgramType::UInt64,
        ),
    ] {
        assert_eq!(
            outcome(expression),
            ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch)
        );
    }
    let overflow = crate::kernel::program_expression::add(
        crate::kernel::program_expression::int32_literal(i32::MAX as u32),
        crate::kernel::program_expression::int32_literal(1),
    );
    assert!(matches!(
        outcome(crate::kernel::program_expression::integer_cast_modulo(
            overflow,
            ProgramType::UInt8
        )),
        ExpressionOutcome::UndefinedBehavior(_)
    ));
    // The explicit rule wraps; an ordinary C narrowing still requires bounds.
    assert_eq!(
        outcome(crate::kernel::program_expression::integer_cast_modulo(
            crate::kernel::program_expression::int64_literal(i64::MAX),
            ProgramType::Int32
        )),
        ExpressionOutcome::Value(ProgramValue::Int32(MachineTerm::constant(u32::MAX)))
    );
    assert!(
        prove_program_expression_evaluation(
            ExecutionState::new(),
            crate::kernel::program_expression::cast(
                crate::kernel::program_expression::int64_literal(i64::MAX),
                ProgramType::Int32
            ),
        )
        .is_none()
    );
}

/// A modular narrowing (C++20, Rust `as`) is the generic `Cast` C
/// builds and files only its destination range: never the identity with
/// its operand that a specification's checked narrowing files beside its
/// range obligations. Filing it made `static_cast<unsigned char>(v)` of a
/// `uint128` (before Stage 4, and of every source after the cast replaced
/// the mask) equal to `v` whatever `v` was, so `v == 511` proved the result
/// `0`.
#[test]
fn a_modular_narrowing_files_its_range_and_no_identity_with_its_operand() {
    for (index, source) in [
        ProgramValue::Int32(MachineTerm::Variable(Variable(983_101))),
        crate::kernel::uint32(MachineTerm::Variable(Variable(983_102))),
        ProgramValue::Int64(MachineTerm::Variable(Variable(983_103))),
        ProgramValue::UInt64(MachineTerm::Variable(Variable(983_104))),
        ProgramValue::Int128(MachineTerm::Variable(Variable(983_105))),
        ProgramValue::UInt128(MachineTerm::Variable(Variable(983_106))),
    ]
    .into_iter()
    .enumerate()
    {
        for target in [
            ProgramType::Int8,
            ProgramType::UInt8,
            ProgramType::Int16,
            ProgramType::UInt16,
        ] {
            let paths = evaluate_program_expression_paths(
                &ExecutionState::new(),
                &crate::kernel::program_expression::integer_cast_modulo(
                    ProgramExpression::Value(source.clone()),
                    target,
                ),
                &PureFactContext::new(),
                &mut ExecutionBudget::default(),
            )
            .expect("a modular narrowing evaluates");
            let [path] = paths.as_slice() else {
                panic!("one path: {paths:?}");
            };
            let ExpressionOutcome::Value(value) = &path.outcome else {
                panic!("{index} -> {target:?}: {:?}", path.outcome);
            };
            assert!(
                matches!(
                    value,
                    crate::kernel::integer_c_value!(MachineTerm::Cast {
                        spelling: MachineCastSpelling::Generic,
                        ..
                    })
                ),
                "{index} -> {target:?}: {value:?}"
            );
            // The narrowing is a value of its own format, whose range is the
            // format's: no range fact is filed for it.
            assert!(path.facts.is_empty(), "{index} -> {target:?}");
            assert!(path.obligations.is_empty(), "{index} -> {target:?}");
        }
    }
}

#[test]
fn unsigned_narrowing_distributes_constant_subtraction_modulo_the_low_word() {
    let value = MachineTerm::Variable(Variable(983_120));
    for decrement in [0, 1, 1u64 << 32, u64::MAX] {
        assert_eq!(
            MachineTerm::uint32_from_64(MachineTerm::uint64_subtract(
                value.clone(),
                MachineTerm::uint64_constant(decrement)
            )),
            MachineTerm::subtract(
                MachineTerm::uint32_from_64(value.clone()),
                MachineTerm::constant(decrement as u32)
            ),
        );
        for input in [0, 1, (1u64 << 32) + 7, u64::MAX] {
            assert_eq!(
                MachineTerm::uint32_from_64(MachineTerm::uint64_subtract(
                    MachineTerm::uint64_constant(input),
                    MachineTerm::uint64_constant(decrement)
                )),
                MachineTerm::constant(input.wrapping_sub(decrement) as u32),
            );
        }
    }
}

/// A pointer at `pair + offset` whose subobject extent is `[pair + start,
/// pair + start + width)`, as `&pair.first` would carry.
fn subobject_pointer(offset: i64, start: i64, width: u32) -> PointerValue {
    PointerValue::new(
        Pointer {
            block: "pair".into(),
            offset: PointerOffsetTerm::Constant(offset),
        },
        ProgramType::Int32Pointer,
    )
    .with_extent(Some(SubobjectExtent {
        start: Pointer {
            block: "pair".into(),
            offset: PointerOffsetTerm::Constant(start),
        },
        width: MachineTerm::constant(width),
    }))
}

fn evaluated_pointer(state: &ExecutionState, expression: ProgramExpression) -> PointerValue {
    let theorem = prove_program_expression_evaluation(state.clone(), expression)
        .expect("the pointer expression should evaluate");
    let Proposition::ProgramExpressionEvaluates {
        outcome: ExpressionOutcome::Value(ProgramValue::Pointer(value)),
        ..
    } = theorem.proposition()
    else {
        panic!("the pointer expression did not produce a pointer");
    };
    value.clone()
}

#[test]
fn pointer_arithmetic_and_casts_keep_the_subobject_extent() {
    let first = subobject_pointer(0, 0, 4);
    let state = ExecutionState::new().with_local("p", ProgramValue::Pointer(first.clone()));

    // One past `first` is still `first`'s pointer: the extent does not move
    // with the address, so the address it now shares with `second` does not
    // make it designate `second`.
    let next = evaluated_pointer(
        &state,
        crate::kernel::program_expression::add(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(1),
        ),
    );
    assert_eq!(next.pointer().offset, PointerOffsetTerm::Constant(4));
    assert_eq!(next.extent(), first.extent());
    let back = evaluated_pointer(
        &state,
        crate::kernel::program_expression::subtract(
            crate::kernel::program_expression::add(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(1),
            ),
            crate::kernel::program_expression::int32_literal(1),
        ),
    );
    assert_eq!(back.extent(), first.extent());

    let cast = evaluated_pointer(
        &state,
        crate::kernel::program_expression::cast(
            crate::kernel::program_expression::variable("p"),
            ProgramType::Int64Pointer,
        ),
    );
    assert_eq!(cast.program_type(), ProgramType::Int64Pointer);
    assert_eq!(cast.extent(), first.extent());
}

#[test]
fn equal_addresses_with_different_extents_are_different_values() {
    let one_past_first = subobject_pointer(4, 0, 4);
    let second = subobject_pointer(4, 4, 4);
    assert_eq!(one_past_first.pointer(), second.pointer());
    assert_ne!(one_past_first, second);
    assert_ne!(
        PointerValue::new(second.pointer().clone(), ProgramType::Int32Pointer),
        second
    );
}

#[test]
fn substitution_maps_the_extent_start_with_the_address() {
    let base = Variable(98_101);
    let address = |delta: i64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::Variable(base),
            PointerOffsetTerm::Constant(delta),
        ),
    };
    let value = ProgramValue::Pointer(
        PointerValue::new(address(4), ProgramType::Int32Pointer).with_extent(Some(
            SubobjectExtent {
                start: address(0),
                width: MachineTerm::constant(4),
            },
        )),
    );
    let replacement = MachineTerm::Variable(Variable(98_102));
    let ProgramValue::Pointer(substituted) =
        substitute_bitvector_variable_in_program_value(&value, base, &replacement)
    else {
        unreachable!();
    };
    let expected =
        |delta: i64| substitute_bitvector_variable_in_pointer(&address(delta), base, &replacement);
    assert_eq!(substituted.pointer(), &expected(4));
    assert_eq!(
        substituted.extent(),
        Some(&SubobjectExtent {
            start: expected(0),
            width: MachineTerm::constant(4),
        })
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/expression_tests.rs");
}

#[test]
fn implicit_byte_pointer_coercion_retains_the_selected_extent() {
    let address = Pointer::symbolic(Variable(22_102));
    let pointer = PointerValue::new(address.clone(), ProgramType::Int8Pointer).with_extent(Some(
        SubobjectExtent {
            start: address,
            width: 4u32.into(),
        },
    ));
    let (value, _) = program_evaluate_speprogram_expression_at_state(
        &ExecutionState::new(),
        &SpecExpression::PointerCoercion(
            Box::new(SpecExpression::Value(ProgramValue::Pointer(
                pointer.clone(),
            ))),
            ProgramType::UInt8Pointer,
        ),
        None,
        &PureFactContext::new(),
    )
    .unwrap();
    let ProgramValue::Pointer(coerced) = value else {
        panic!("a pointer coercion must yield a pointer")
    };
    assert_eq!(coerced.program_type(), ProgramType::UInt8Pointer);
    assert_eq!(coerced.designation(), pointer.designation());
    assert_eq!(coerced.opaque_extent(), pointer.opaque_extent());
    assert_eq!(coerced.extent(), pointer.extent());
    for source in [ProgramType::Int8Pointer, ProgramType::UInt8Pointer] {
        for target in [ProgramType::Int8Pointer, ProgramType::UInt8Pointer] {
            let (value, _) = program_evaluate_speprogram_expression_at_state(
                &ExecutionState::new(),
                &SpecExpression::Cast(
                    Box::new(SpecExpression::Value(ProgramValue::Pointer(
                        pointer.clone().with_type(source),
                    ))),
                    target,
                ),
                None,
                &PureFactContext::new(),
            )
            .unwrap();
            let ProgramValue::Pointer(explicit) = value else {
                panic!("a pointer cast must yield a pointer")
            };
            assert_eq!(explicit.program_type(), target);
            assert_eq!(explicit.designation(), pointer.designation());
            assert_eq!(explicit.opaque_extent(), pointer.opaque_extent());
            assert_eq!(explicit.extent(), pointer.extent());
        }
    }
    for (source, target) in [
        (ProgramType::Int32Pointer, ProgramType::UInt8Pointer),
        (ProgramType::VoidPointer, ProgramType::UInt8Pointer),
        (ProgramType::Int8Pointer, ProgramType::VoidPointer),
        (ProgramType::VoidPointer, ProgramType::VoidPointer),
    ] {
        let (value, _) = program_evaluate_speprogram_expression_at_state(
            &ExecutionState::new(),
            &SpecExpression::Cast(
                Box::new(SpecExpression::Value(ProgramValue::Pointer(
                    pointer.clone().with_type(source),
                ))),
                target,
            ),
            None,
            &PureFactContext::new(),
        )
        .unwrap();
        let ProgramValue::Pointer(explicit) = value else {
            panic!("a pointer cast must yield a pointer")
        };
        assert!(explicit.extent_is_known());
        assert!(explicit.extent().is_none());
    }
}

#[test]
fn complete_pointer_reads_keep_stored_bounds_across_different_cells() {
    let _session = crate::kernel::VerificationSession::enter();
    let a = Pointer::symbolic(Variable(22_111));
    let b = Pointer::symbolic(Variable(22_112));
    let stored = subobject_pointer(0, 0, 4);
    let before_b = Memory::new().store(a.clone(), ProgramValue::Pointer(stored.clone()));
    let memory = before_b
        .clone()
        .store(b.clone(), ProgramValue::Pointer(stored.clone()));
    let read = |memory: &Memory, address: &Pointer| {
        PointerValue::from_read(
            stored.pointer().clone(),
            ProgramType::Int32Pointer,
            &crate::kernel::intern_memory_ref(memory),
            address,
        )
    };
    let separation = |left: MemoryRange, right: MemoryRange| {
        crate::kernel::region_footprint::byte_premise(&Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(left)),
            right: Box::new(Resource::Memory(right)),
        })
        .unwrap()
    };
    let context = PureFactContext::new().assume_proposition(separation(
        memory_range(a.clone(), 0, 2),
        memory_range(b.clone(), 0, 2),
    ));
    let (_, _, equality) = super::explicit_frame(
        &before_b,
        &memory,
        &a,
        ProgramType::Int32Pointer,
        &[Proposition::MemoryMutatesOnly {
            before: before_b.clone(),
            after: memory.clone(),
            writes: vec![(b.clone(), 8)],
        }],
        &context,
    )
    .expect("separate pointer cell survives the selected write");
    let context = context.assume_proposition(equality);
    let first = read(&memory, &a);
    let second = read(&memory, &b);
    assert!(context.pointer_designations_match(&first, &stored));
    assert!(context.pointer_designations_match(&first, &second));
    assert!(!context.pointer_designations_match(&first.clone().with_root_extent(), &stored));
    assert!(!context.pointer_designations_match(
        &first.clone().with_extent(Some(SubobjectExtent {
            start: stored.pointer().clone(),
            width: 2u32.into(),
        })),
        &stored,
    ));
    let c = Pointer::symbolic(Variable(22_113));
    let before = Memory::new();
    let original = read(&before, &c);
    let changed = before.clone().store(b.clone(), int32(1));
    let later = read(&changed, &c);
    let copied = changed
        .clone()
        .store(a.clone(), ProgramValue::Pointer(later));
    let framed = context
        .clone()
        .assume_proposition(separation(
            memory_range(c.clone(), 0, 2),
            memory_range(b.clone(), 0, 1),
        ))
        .assume_proposition(separation(
            memory_range(c.clone(), 0, 2),
            memory_range(a.clone(), 0, 2),
        ));
    let (_, _, equality) = super::explicit_frame(
        &before,
        &changed,
        &c,
        ProgramType::Int32Pointer,
        &[Proposition::MemoryMutatesOnly {
            before: before.clone(),
            after: changed.clone(),
            writes: vec![(b.clone(), 4)],
        }],
        &framed,
    )
    .expect("the selected write preserves the copied pointer's source");
    let framed = framed.assume_proposition(equality);
    assert!(framed.pointer_designations_match(&read(&copied, &a), &original));
    assert!(!context.pointer_designations_match(&first, &stored.clone().with_root_extent()));
    let partial = memory.store(a.clone().offset_by_bytes(4), int32(0));
    assert!(!context.pointer_designations_match(&read(&partial, &a), &stored));
    let numeric = Memory::new().store(
        a.clone(),
        ProgramValue::UInt64(MachineTerm::pointer_address(stored.pointer().clone())),
    );
    assert!(!context.pointer_designations_match(&read(&numeric, &a), &stored));
}

fn checked_term(value: &ProgramValue) -> MachineTerm {
    match value {
        ProgramValue::Int8(term) => term.clone(),
        other => panic!("{other:?}"),
    }
}

#[test]
fn array_index_conversion_is_independent_of_bounds() {
    let _session = crate::kernel::VerificationSession::enter();
    let i = MachineTerm::Variable(Variable(989_970));
    let empty = PureFactContext::new();
    let bounded = empty.clone().assume_condition(
        ConditionTerm::unsigned_less_than(i.clone(), MachineTerm::uint32_constant(4)),
        true,
    );
    let base = ProgramValue::typed_pointer(
        Pointer::symbolic(Variable(989_972)),
        ProgramType::Int32Pointer,
    );
    for index in [
        ProgramValue::Int32(i.clone()),
        ProgramValue::UInt32(i.clone()),
        ProgramValue::UInt64(i.clone()),
    ] {
        let expression = SpecExpression::PointerOffset {
            pointer: Box::new(SpecExpression::ProgramExpression(ProgramExpression::Value(
                base.clone(),
            ))),
            elements: Box::new(SpecExpression::ProgramExpression(ProgramExpression::Value(
                index,
            ))),
            byte_width: 4,
        };
        let lower = |facts: &PureFactContext| {
            crate::kernel::spec::evaluate_spec_expression_paths_with_bindings(
                &ExecutionState::new(),
                &expression,
                facts,
                &BTreeMap::new(),
                &mut ExecutionBudget::default(),
            )
            .unwrap()
            .into_iter()
            .map(|path| path.value)
            .collect::<Vec<_>>()
        };
        let plain = lower(&empty);
        assert_eq!(plain.len(), 1);
        assert_eq!(plain, lower(&bounded));
    }
}

#[test]
fn widened_index_bounds_use_the_full_unsigned_value() {
    let x = MachineTerm::Variable(Variable(989_973));
    let wide = MachineTerm::uint64_from_32(x.clone());
    let bounded = PureFactContext::new().assume_condition(
        ConditionTerm::unsigned_less_than(x.clone(), MachineTerm::uint32_constant(4)),
        true,
    );
    assert!(bounded.uint64_index_fits_int32(&wide));
    // A bound on a low word is not a bound on an unrelated native wide value.
    assert!(!bounded.uint64_index_fits_int32(&x));
    let high = PureFactContext::new().assume_condition(
        ConditionTerm::unsigned_less_than(MachineTerm::uint32_constant(i32::MAX as u32), x.clone()),
        true,
    );
    assert!(!high.uint64_index_fits_int32(&wide));
    assert_eq!(
        high.decide(&ConditionTerm::uint64_greater_than(
            wide,
            MachineTerm::uint64_constant(i32::MAX as u64)
        )),
        Some(true)
    );
}

#[test]
fn index_observation_follows_machine_arithmetic() {
    let base = Pointer::symbolic(Variable(989_974));
    let leaf = |value| SpecExpression::ProgramExpression(ProgramExpression::Value(value));
    for (index, bytes) in [
        (
            leaf(ProgramValue::Int32(MachineTerm::constant(u32::MAX))),
            -4,
        ),
        (
            leaf(ProgramValue::UInt32(MachineTerm::uint32_constant(u32::MAX))),
            4 * i64::from(u32::MAX),
        ),
        (
            SpecExpression::Add(
                Box::new(leaf(ProgramValue::UInt32(MachineTerm::uint32_constant(
                    u32::MAX,
                )))),
                Box::new(leaf(ProgramValue::UInt32(MachineTerm::uint32_constant(1)))),
            ),
            0,
        ),
    ] {
        let expression = SpecExpression::PointerOffset {
            pointer: Box::new(leaf(ProgramValue::typed_pointer(
                base.clone(),
                ProgramType::Int32Pointer,
            ))),
            elements: Box::new(index),
            byte_width: 4,
        };
        let paths = crate::kernel::spec::evaluate_spec_expression_paths_with_bindings(
            &ExecutionState::new(),
            &expression,
            &PureFactContext::new(),
            &BTreeMap::new(),
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        assert_eq!(paths.len(), 1);
        let ProgramValue::Pointer(value) = &paths[0].value.clone().into_native() else {
            panic!("pointer result")
        };
        assert_eq!(value.pointer().offset, PointerOffsetTerm::Constant(bytes));
    }
}

#[test]
fn tag_clearing_lowering_keeps_the_written_word_under_bounds() {
    let word = MachineTerm::Variable(Variable(989_990));
    let tag = MachineTerm::Variable(Variable(989_991));
    let mask = MachineTerm::uint64_constant(!3);
    let bounded = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(0u32.into(), tag.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(tag.clone(), 1u32.into()),
            true,
        )
        .assume_condition(
            ConditionTerm::uint64_equal(
                MachineTerm::uint64_bitwise_and(word.clone(), MachineTerm::uint64_constant(1)),
                MachineTerm::uint64_constant(0),
            ),
            true,
        );
    for inner in [
        MachineTerm::uint64_bitwise_or(word.clone(), MachineTerm::uint64_from_int32(tag)),
        MachineTerm::uint64_add(word, MachineTerm::uint64_constant(1)),
    ] {
        let leaf = |term| {
            SpecExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::UInt64(term)))
        };
        let expression =
            SpecExpression::BitwiseAnd(Box::new(leaf(inner.clone())), Box::new(leaf(mask.clone())));
        let expected = ProgramValue::UInt64(MachineTerm::uint64_bitwise_and(inner, mask.clone()));
        for facts in [&PureFactContext::new(), &bounded] {
            let paths = crate::kernel::spec::evaluate_spec_expression_paths_with_bindings(
                &ExecutionState::new(),
                &expression,
                facts,
                &BTreeMap::new(),
                &mut ExecutionBudget::default(),
            )
            .unwrap();
            assert_eq!(paths.len(), 1);
            assert_eq!(paths[0].value.clone().into_native(), expected);
        }
    }
}

#[test]
fn specification_volatile_reads_do_not_create_execution_events() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer {
        block: "cell".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let initial = ExecutionState::new()
        .with_resource_context(own_memory_context(pointer.clone(), 0, 1))
        .with_memory(
            Memory::new()
                .with_block("cell", 4)
                .store(pointer.clone(), int32(7)),
        );
    let function = program_function(
        ProgramType::Int32,
        "f",
        vec![
            program_parameter("value", ProgramType::Int32).with_volatile(true),
            program_parameter("p", ProgramType::Int32Pointer).with_pointee_volatile(true),
        ],
        program_return(crate::kernel::program_expression::variable("value")),
    );
    let state = bind_program_function_arguments(
        &initial,
        &function,
        &[
            int32(7),
            ProgramValue::typed_pointer(pointer, ProgramType::Int32Pointer),
        ],
    )
    .unwrap();
    let _specification = crate::kernel::eval::SpecificationReadScope::enter();
    for expression in [
        crate::kernel::program_expression::variable("value"),
        crate::kernel::program_expression::typed_load(
            crate::kernel::program_expression::variable("p"),
            ProgramType::Int32,
        ),
    ] {
        let paths = evaluate_program_expression_paths(
            &state,
            &expression,
            &PureFactContext::new(),
            &mut ExecutionBudget::beside_live_state(),
        )
        .expect("a specification must not allocate an execution event");
        assert_eq!(paths.len(), 1);
        assert!(
            matches!(paths[0].outcome, ExpressionOutcome::Value(_)),
            "{expression:?}: {:?}",
            paths[0].outcome
        );
        assert!(
            paths[0]
                .facts
                .iter()
                .all(|fact| fact.volatile_read_result().is_none())
        );
    }
}

#[test]
fn unsigned_division_reports_its_domain_even_when_already_known() {
    let _session = crate::kernel::VerificationSession::enter();
    let left = MachineTerm::Variable(Variable(991_601));
    let right = MachineTerm::Variable(Variable(991_602));
    let zero = ConditionTerm::machine_compare(
        MachineIntegerType::UInt32,
        crate::kernel::CompareRelation::Equal,
        right.clone(),
        MachineTerm::constant(0),
    );
    for known in [None, Some(false), Some(true)] {
        let assumptions = known.map_or_else(PureFactContext::new, |value| {
            PureFactContext::new().assume_condition(zero.clone(), value)
        });
        for remainder in [false, true] {
            let apply = if remainder {
                crate::kernel::eval::apply_program_remainder
            } else {
                crate::kernel::eval::apply_program_divide
            };
            let paths = apply(
                ProgramValue::UInt32(left.clone()),
                ProgramValue::UInt32(right.clone()),
                vec![].into(),
                vec![],
                &assumptions,
            );
            assert_eq!(paths.len(), 1, "one conditional successor, {known:?}");
            assert!(matches!(
                paths[0].outcome,
                ExpressionOutcome::Value(ProgramValue::UInt32(_))
            ));
            assert_eq!(
                paths[0].obligations.len(),
                1,
                "always retain the domain, {known:?}"
            );
            assert_eq!(
                paths[0].obligations[0].proposition(),
                &Proposition::ConditionIs(zero.clone(), false)
            );
        }
    }
}
