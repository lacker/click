use super::*;

#[test]
fn constructors_evaluate_to_unary_lists() {
    assert_evaluates_to(succ_call(zero()), one_value());
    assert_evaluates_to(succ_call(one_value()), two_value());
    assert_evaluates_to(is_zero_call(zero()), true_value());
    assert_evaluates_to(is_zero_call(one_value()), false_value());
    assert_evaluates_to(pred_call(zero()), nil());
    assert_evaluates_to(pred_call(three_value()), two_value());
    assert_evaluates_to(add_call(two_value(), one_value()), three_value());
    assert_evaluates_to(add_call(two_value(), zero()), two_value());
    assert_evaluates_to(sub_call(three_value(), one_value()), two_value());
    assert_evaluates_to(sub_call(one_value(), three_value()), nil());
    assert_evaluates_to(sub_call(three_value(), zero()), three_value());
    assert_evaluates_to(sub_call(zero(), three_value()), nil());
    assert_evaluates_to(
        add_call(add_call(one_value(), two_value()), one_value()),
        four_value(),
    );
    assert_evaluates_to(mul_call(zero(), three_value()), nil());
    assert_evaluates_to(mul_call(three_value(), zero()), nil());
    assert_evaluates_to(mul_call(one_value(), three_value()), three_value());
    assert_evaluates_to(mul_call(two_value(), three_value()), six_value());
    assert_evaluates_to(nat_eq_call(two_value(), two_value()), true_value());
    assert_evaluates_to(nat_eq_call(two_value(), three_value()), false_value());
    assert_evaluates_to(nat_le_call(zero(), three_value()), true_value());
    assert_evaluates_to(nat_le_call(two_value(), two_value()), true_value());
    assert_evaluates_to(nat_le_call(three_value(), two_value()), false_value());
    assert_evaluates_to(nat_lt_call(zero(), one_value()), true_value());
    assert_evaluates_to(nat_lt_call(two_value(), two_value()), false_value());
    assert_evaluates_to(nat_lt_call(two_value(), three_value()), true_value());
    assert_evaluates_to(nat_lt_call(three_value(), two_value()), false_value());
}

#[test]
fn is_nat_value_accepts_unary_lists() {
    assert_evaluates_to(is_nat_value_call(nil()), true_value());
    assert_evaluates_to(is_nat_value_call(one_value()), true_value());
    assert_evaluates_to(is_nat_value_call(three_value()), true_value());
}

#[test]
fn is_nat_value_rejects_other_values() {
    assert_evaluates_to(is_nat_value_call(quote(NOT_UNIT)), false_value());
    assert_evaluates_to(
        is_nat_value_call(cons(quote(NOT_UNIT), nil())),
        false_value(),
    );
    assert_evaluates_to(
        is_nat_value_call(Computation::Lambda(Lambda {
            parameter: NAT,
            body: Box::new(var(NAT)),
        })),
        false_value(),
    );
}

fn assert_evaluates_to(computation: Computation, expected: Computation) {
    let expected = expected
        .as_value()
        .expect("expected nat test result should be a value");
    let proof = proof_by_evaluation(computation.clone(), expected.clone(), 256)
        .expect("nat computation should evaluate");

    assert!(check_evaluates_to(computation, expected, &proof));
}
