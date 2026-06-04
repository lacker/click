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

pub fn add() -> Computation {
    computation_ref("add")
}

pub fn add_definition() -> Computation {
    definition("add")
}

pub fn succ_call(nat: Computation) -> Computation {
    apply(succ(), nat)
}

pub fn is_nat_value_call(value: Computation) -> Computation {
    apply(is_nat_value(), value)
}

pub fn add_call(left: Computation, right: Computation) -> Computation {
    apply(apply(add(), left), right)
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

pub fn succ_computes_to_list_source_theorem() -> Prop {
    theorem_prop("succ_computes_to_list")
}

pub fn succ_preserves_nat_value_source_theorem() -> Prop {
    theorem_prop("succ_preserves_nat_value")
}

pub fn is_nat_value_cons_source_theorem() -> Prop {
    theorem_prop("is_nat_value_cons")
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
        add(),
        Computation::Ref(super::computation_name("add").unwrap())
    );
}

#[test]
fn nat_theorem_statements_load_from_source() {
    let zero_result = theorem_symbol("zero_computes_to_list", "result");
    let add_zero_left_right = theorem_symbol("add_zero_left", "right");
    let add_zero_right_nat = theorem_symbol("add_zero_right", "nat");

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
}

#[test]
fn constructors_evaluate_to_unary_lists() {
    assert_evaluates_to(succ_call(zero()), one_value());
    assert_evaluates_to(succ_call(one_value()), two_value());
    assert_evaluates_to(add_call(two_value(), one_value()), three_value());
    assert_evaluates_to(add_call(two_value(), zero()), two_value());
    assert_evaluates_to(
        add_call(add_call(one_value(), two_value()), one_value()),
        four_value(),
    );
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
    assert_theory_has_theorem(&theory, "add_zero_left", add_zero_left_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "add_computes_to_list",
        add_computes_to_list_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "add_cons", add_cons_source_theorem());
    assert_theory_has_theorem(&theory, "add_succ_left", add_succ_left_source_theorem());
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
}

fn assert_theory_has_theorem(theory: &Theory, spelling: &str, prop: Prop) {
    let name = super::theorem_name(spelling).expect("prelude should define theorem name");

    assert_eq!(theory.theorem(name), Some(&prop));
}
