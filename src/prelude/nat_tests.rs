//! Test helpers and expected behavior for the nat prelude source.

use crate::{Computation, Lambda, Prop, Symbol, Theory, computes_to, computes_to_list, is_list};

use super::list_tests::{
    apply, check_evaluates_to, cons, false_value, nil, proof_by_evaluation, quote, true_value,
    unit, var,
};

const NAT: Symbol = Symbol(2_100);
const NOT_UNIT: Symbol = Symbol(2_104);

fn computation_ref(spelling: &str) -> Computation {
    Computation::Ref(super::computation_name(spelling).expect("prelude should define computation"))
}

pub fn zero() -> Computation {
    computation_ref("zero")
}

pub fn zero_definition() -> Computation {
    definition("zero")
}

pub fn succ() -> Computation {
    computation_ref("succ")
}

pub fn succ_definition() -> Computation {
    definition("succ")
}

pub fn is_nat_value() -> Computation {
    computation_ref("is-nat-value")
}

pub fn is_nat_value_definition() -> Computation {
    definition("is-nat-value")
}

pub fn is_zero() -> Computation {
    computation_ref("is-zero")
}

pub fn is_zero_definition() -> Computation {
    definition("is-zero")
}

pub fn pred() -> Computation {
    computation_ref("pred")
}

pub fn pred_definition() -> Computation {
    definition("pred")
}

pub fn add() -> Computation {
    computation_ref("add")
}

pub fn add_definition() -> Computation {
    definition("add")
}

pub fn mul() -> Computation {
    computation_ref("mul")
}

pub fn mul_definition() -> Computation {
    definition("mul")
}

pub fn succ_call(nat: Computation) -> Computation {
    apply(succ(), nat)
}

pub fn is_nat_value_call(value: Computation) -> Computation {
    apply(is_nat_value(), value)
}

pub fn is_zero_call(nat: Computation) -> Computation {
    apply(is_zero(), nat)
}

pub fn pred_call(nat: Computation) -> Computation {
    apply(pred(), nat)
}

pub fn add_call(left: Computation, right: Computation) -> Computation {
    apply(apply(add(), left), right)
}

pub fn mul_call(left: Computation, right: Computation) -> Computation {
    apply(apply(mul(), left), right)
}

pub fn one_value() -> Computation {
    cons(unit(), nil())
}

pub fn two_value() -> Computation {
    cons(unit(), one_value())
}

pub fn three_value() -> Computation {
    cons(unit(), two_value())
}

pub fn four_value() -> Computation {
    cons(unit(), three_value())
}

pub fn five_value() -> Computation {
    cons(unit(), four_value())
}

pub fn six_value() -> Computation {
    cons(unit(), five_value())
}

pub fn add_is_append_source_theorem() -> Prop {
    theorem_prop("add_is_append")
}

pub fn zero_computes_to_list_source_theorem() -> Prop {
    theorem_prop("zero_computes_to_list")
}

pub fn zero_is_nat_value_source_theorem() -> Prop {
    theorem_prop("zero_is_nat_value")
}

pub fn succ_zero_source_theorem() -> Prop {
    theorem_prop("succ_zero")
}

pub fn is_zero_zero_source_theorem() -> Prop {
    theorem_prop("is_zero_zero")
}

pub fn is_zero_succ_source_theorem() -> Prop {
    theorem_prop("is_zero_succ")
}

pub fn pred_zero_source_theorem() -> Prop {
    theorem_prop("pred_zero")
}

pub fn pred_succ_source_theorem() -> Prop {
    theorem_prop("pred_succ")
}

pub fn pred_computes_to_list_source_theorem() -> Prop {
    theorem_prop("pred_computes_to_list")
}

pub fn succ_computes_to_list_source_theorem() -> Prop {
    theorem_prop("succ_computes_to_list")
}

pub fn succ_preserves_nat_value_source_theorem() -> Prop {
    theorem_prop("succ_preserves_nat_value")
}

pub fn is_nat_value_cons_source_theorem() -> Prop {
    theorem_prop("is_nat_value_cons")
}

pub fn is_nat_value_cons_true_elim_source_theorem() -> Prop {
    theorem_prop("is_nat_value_cons_true_elim")
}

pub fn add_zero_left_source_theorem() -> Prop {
    theorem_prop("add_zero_left")
}

pub fn add_computes_to_list_source_theorem() -> Prop {
    theorem_prop("add_computes_to_list")
}

pub fn add_cons_source_theorem() -> Prop {
    theorem_prop("add_cons")
}

pub fn add_succ_left_source_theorem() -> Prop {
    theorem_prop("add_succ_left")
}

pub fn add_cons_unit_right_source_theorem() -> Prop {
    theorem_prop("add_cons_unit_right")
}

pub fn add_succ_right_source_theorem() -> Prop {
    theorem_prop("add_succ_right")
}

pub fn add_zero_right_source_theorem() -> Prop {
    theorem_prop("add_zero_right")
}

pub fn add_nat_suffix_preserves_nat_value_source_theorem() -> Prop {
    theorem_prop("add_nat_suffix_preserves_nat_value")
}

pub fn add_preserves_nat_value_source_theorem() -> Prop {
    theorem_prop("add_preserves_nat_value")
}

pub fn add_assoc_source_theorem() -> Prop {
    theorem_prop("add_assoc")
}

pub fn add_comm_source_theorem() -> Prop {
    theorem_prop("add_comm")
}

pub fn add_swap_source_theorem() -> Prop {
    theorem_prop("add_swap")
}

pub fn mul_zero_left_source_theorem() -> Prop {
    theorem_prop("mul_zero_left")
}

pub fn mul_cons_source_theorem() -> Prop {
    theorem_prop("mul_cons")
}

pub fn mul_computes_to_list_source_theorem() -> Prop {
    theorem_prop("mul_computes_to_list")
}

pub fn mul_preserves_nat_value_source_theorem() -> Prop {
    theorem_prop("mul_preserves_nat_value")
}

pub fn mul_succ_left_source_theorem() -> Prop {
    theorem_prop("mul_succ_left")
}

pub fn mul_succ_right_source_theorem() -> Prop {
    theorem_prop("mul_succ_right")
}

pub fn mul_zero_right_source_theorem() -> Prop {
    theorem_prop("mul_zero_right")
}

pub fn mul_one_left_source_theorem() -> Prop {
    theorem_prop("mul_one_left")
}

pub fn mul_one_right_source_theorem() -> Prop {
    theorem_prop("mul_one_right")
}

pub fn mul_comm_source_theorem() -> Prop {
    theorem_prop("mul_comm")
}

pub fn mul_add_left_distrib_source_theorem() -> Prop {
    theorem_prop("mul_add_left_distrib")
}

pub fn mul_assoc_source_theorem() -> Prop {
    theorem_prop("mul_assoc")
}

pub fn mul_add_right_distrib_source_theorem() -> Prop {
    theorem_prop("mul_add_right_distrib")
}

fn definition(spelling: &str) -> Computation {
    let module = super::parsed_nat_module().expect("prelude nat source should parse");
    let env = super::parsed_prelude_env().expect("prelude source should parse");
    let name = env
        .computation(spelling)
        .expect("prelude nat source should define requested computation name");

    module
        .computation(name)
        .cloned()
        .expect("prelude nat source should define requested computation")
}

fn theorem_prop(spelling: &str) -> Prop {
    theorem_definition(spelling).prop
}

fn theorem_definition(spelling: &str) -> crate::elab::source::ParsedTheorem {
    let module = super::parsed_nat_module().expect("prelude nat source should parse");
    let env = super::parsed_prelude_env().expect("prelude source should parse");
    let name = env
        .theorem(spelling)
        .expect("prelude nat source should define requested theorem name");

    module
        .theorem(name)
        .cloned()
        .expect("prelude nat source should define requested theorem")
}

fn theorem_symbol(theorem: &str, spelling: &str) -> Symbol {
    theorem_definition(theorem)
        .symbol(spelling)
        .expect("prelude nat source should define requested theorem symbol once")
}

#[test]
fn nat_definitions_load_from_source() {
    assert_eq!(zero_definition(), nil());
    assert_eq!(
        succ(),
        Computation::Ref(super::computation_name("succ").unwrap())
    );
    assert_eq!(
        is_nat_value(),
        Computation::Ref(super::computation_name("is-nat-value").unwrap())
    );
    assert_eq!(
        is_zero(),
        Computation::Ref(super::computation_name("is-zero").unwrap())
    );
    assert_eq!(
        pred(),
        Computation::Ref(super::computation_name("pred").unwrap())
    );
    assert_eq!(
        add(),
        Computation::Ref(super::computation_name("add").unwrap())
    );
    assert_eq!(
        mul(),
        Computation::Ref(super::computation_name("mul").unwrap())
    );
}

#[test]
fn nat_theorem_statements_load_from_source() {
    let zero_result = theorem_symbol("zero_computes_to_list", "result");
    let pred_succ_nat = theorem_symbol("pred_succ", "nat");
    let pred_result = theorem_symbol("pred_computes_to_list", "result");
    let pred_nat = theorem_symbol("pred_computes_to_list", "nat");
    let add_zero_left_right = theorem_symbol("add_zero_left", "right");
    let add_zero_right_nat = theorem_symbol("add_zero_right", "nat");
    let mul_result = theorem_symbol("mul_computes_to_list", "result");
    let mul_left = theorem_symbol("mul_computes_to_list", "left");
    let mul_right = theorem_symbol("mul_computes_to_list", "right");
    let mul_zero_right_nat = theorem_symbol("mul_zero_right", "nat");
    let mul_one_left_right = theorem_symbol("mul_one_left", "right");

    assert_eq!(
        zero_computes_to_list_source_theorem(),
        computes_to_list(zero_result, zero())
    );
    assert_eq!(
        zero_is_nat_value_source_theorem(),
        computes_to(is_nat_value_call(zero()), true_value())
    );
    assert_eq!(
        succ_zero_source_theorem(),
        computes_to(succ_call(zero()), one_value())
    );
    assert_eq!(
        pred_succ_source_theorem(),
        crate::forall_where(
            pred_succ_nat,
            is_list(var(pred_succ_nat)),
            computes_to(pred_call(succ_call(var(pred_succ_nat))), var(pred_succ_nat))
        )
    );
    assert_eq!(
        pred_computes_to_list_source_theorem(),
        crate::forall_where(
            pred_nat,
            is_list(var(pred_nat)),
            computes_to_list(pred_result, pred_call(var(pred_nat)))
        )
    );
    assert_eq!(
        add_zero_left_source_theorem(),
        crate::forall_where(
            add_zero_left_right,
            is_list(var(add_zero_left_right)),
            computes_to(
                add_call(zero(), var(add_zero_left_right)),
                var(add_zero_left_right)
            )
        )
    );
    assert_eq!(
        add_zero_right_source_theorem(),
        crate::forall_where(
            add_zero_right_nat,
            is_list(var(add_zero_right_nat)),
            computes_to(
                add_call(var(add_zero_right_nat), zero()),
                var(add_zero_right_nat)
            )
        )
    );
    assert_eq!(
        mul_computes_to_list_source_theorem(),
        crate::forall_where(
            mul_left,
            is_list(var(mul_left)),
            crate::forall_where(
                mul_right,
                is_list(var(mul_right)),
                computes_to_list(mul_result, mul_call(var(mul_left), var(mul_right)))
            )
        )
    );
    assert_eq!(
        mul_zero_right_source_theorem(),
        crate::forall_where(
            mul_zero_right_nat,
            is_list(var(mul_zero_right_nat)),
            computes_to(mul_call(var(mul_zero_right_nat), zero()), zero())
        )
    );
    assert_eq!(
        mul_one_left_source_theorem(),
        crate::forall_where(
            mul_one_left_right,
            is_list(var(mul_one_left_right)),
            computes_to(
                mul_call(succ_call(zero()), var(mul_one_left_right)),
                var(mul_one_left_right)
            )
        )
    );
}

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
    assert_evaluates_to(
        add_call(add_call(one_value(), two_value()), one_value()),
        four_value(),
    );
    assert_evaluates_to(mul_call(zero(), three_value()), nil());
    assert_evaluates_to(mul_call(three_value(), zero()), nil());
    assert_evaluates_to(mul_call(one_value(), three_value()), three_value());
    assert_evaluates_to(mul_call(two_value(), three_value()), six_value());
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

#[test]
fn checked_theory_contains_nat_theorems() {
    let theory = super::theory();

    assert_theory_has_theorem(&theory, "add_is_append", add_is_append_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "zero_computes_to_list",
        zero_computes_to_list_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "zero_is_nat_value",
        zero_is_nat_value_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "succ_zero", succ_zero_source_theorem());
    assert_theory_has_theorem(&theory, "is_zero_zero", is_zero_zero_source_theorem());
    assert_theory_has_theorem(&theory, "is_zero_succ", is_zero_succ_source_theorem());
    assert_theory_has_theorem(&theory, "pred_zero", pred_zero_source_theorem());
    assert_theory_has_theorem(&theory, "pred_succ", pred_succ_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "pred_computes_to_list",
        pred_computes_to_list_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "succ_computes_to_list",
        succ_computes_to_list_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "succ_preserves_nat_value",
        succ_preserves_nat_value_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "is_nat_value_cons",
        is_nat_value_cons_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "is_nat_value_cons_true_elim",
        is_nat_value_cons_true_elim_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "add_zero_left", add_zero_left_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "add_computes_to_list",
        add_computes_to_list_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "add_cons", add_cons_source_theorem());
    assert_theory_has_theorem(&theory, "add_succ_left", add_succ_left_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "add_cons_unit_right",
        add_cons_unit_right_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "add_succ_right", add_succ_right_source_theorem());
    assert_theory_has_theorem(&theory, "add_zero_right", add_zero_right_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "add_nat_suffix_preserves_nat_value",
        add_nat_suffix_preserves_nat_value_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "add_preserves_nat_value",
        add_preserves_nat_value_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "add_assoc", add_assoc_source_theorem());
    assert_theory_has_theorem(&theory, "add_comm", add_comm_source_theorem());
    assert_theory_has_theorem(&theory, "add_swap", add_swap_source_theorem());
    assert_theory_has_theorem(&theory, "mul_zero_left", mul_zero_left_source_theorem());
    assert_theory_has_theorem(&theory, "mul_cons", mul_cons_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "mul_computes_to_list",
        mul_computes_to_list_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "mul_preserves_nat_value",
        mul_preserves_nat_value_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "mul_succ_left", mul_succ_left_source_theorem());
    assert_theory_has_theorem(&theory, "mul_succ_right", mul_succ_right_source_theorem());
    assert_theory_has_theorem(&theory, "mul_zero_right", mul_zero_right_source_theorem());
    assert_theory_has_theorem(&theory, "mul_one_left", mul_one_left_source_theorem());
    assert_theory_has_theorem(&theory, "mul_one_right", mul_one_right_source_theorem());
    assert_theory_has_theorem(&theory, "mul_comm", mul_comm_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "mul_add_left_distrib",
        mul_add_left_distrib_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "mul_assoc", mul_assoc_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "mul_add_right_distrib",
        mul_add_right_distrib_source_theorem(),
    );
}

fn assert_theory_has_theorem(theory: &Theory, spelling: &str, prop: Prop) {
    let name = super::theorem_name(spelling).expect("prelude should define theorem name");

    assert_eq!(theory.theorem(name), Some(&prop));
}
