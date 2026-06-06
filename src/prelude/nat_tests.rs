//! Test helpers and expected behavior for the nat prelude source.

use crate::{
    Computation, Lambda, Prop, Symbol, Theory, computes_to, computes_to_list, implies, is_bool,
    is_list, is_value, or,
};

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

pub fn sub() -> Computation {
    computation_ref("sub")
}

pub fn mul() -> Computation {
    computation_ref("mul")
}

pub fn mul_definition() -> Computation {
    definition("mul")
}

pub fn nat_eq() -> Computation {
    computation_ref("nat-eq")
}

pub fn nat_le() -> Computation {
    computation_ref("nat-le")
}

pub fn nat_lt() -> Computation {
    computation_ref("nat-lt")
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

pub fn sub_call(left: Computation, right: Computation) -> Computation {
    apply(apply(sub(), left), right)
}

pub fn mul_call(left: Computation, right: Computation) -> Computation {
    apply(apply(mul(), left), right)
}

pub fn nat_eq_call(left: Computation, right: Computation) -> Computation {
    apply(apply(nat_eq(), left), right)
}

pub fn nat_le_call(left: Computation, right: Computation) -> Computation {
    apply(apply(nat_le(), left), right)
}

pub fn nat_lt_call(left: Computation, right: Computation) -> Computation {
    apply(apply(nat_lt(), left), right)
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

pub fn zero_eq_nil_source_theorem() -> Prop {
    theorem_prop("zero_eq_nil")
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

pub fn is_zero_is_bool_source_theorem() -> Prop {
    theorem_prop("is_zero_is_bool")
}

pub fn pred_zero_source_theorem() -> Prop {
    theorem_prop("pred_zero")
}

pub fn pred_succ_source_theorem() -> Prop {
    theorem_prop("pred_succ")
}

pub fn is_zero_pred_succ_source_theorem() -> Prop {
    theorem_prop("is_zero_pred_succ")
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

pub fn nat_eq_zero_zero_source_theorem() -> Prop {
    theorem_prop("nat_eq_zero_zero")
}

pub fn nat_eq_zero_succ_source_theorem() -> Prop {
    theorem_prop("nat_eq_zero_succ")
}

pub fn nat_eq_succ_zero_source_theorem() -> Prop {
    theorem_prop("nat_eq_succ_zero")
}

pub fn nat_eq_succ_succ_source_theorem() -> Prop {
    theorem_prop("nat_eq_succ_succ")
}

pub fn nat_eq_zero_left_source_theorem() -> Prop {
    theorem_prop("nat_eq_zero_left")
}

pub fn nat_eq_zero_right_source_theorem() -> Prop {
    theorem_prop("nat_eq_zero_right")
}

pub fn nat_eq_refl_source_theorem() -> Prop {
    theorem_prop("nat_eq_refl")
}

pub fn nat_eq_is_bool_source_theorem() -> Prop {
    theorem_prop("nat_eq_is_bool")
}

pub fn nat_eq_pred_succ_source_theorem() -> Prop {
    theorem_prop("nat_eq_pred_succ")
}

pub fn nat_le_zero_left_source_theorem() -> Prop {
    theorem_prop("nat_le_zero_left")
}

pub fn nat_le_zero_right_source_theorem() -> Prop {
    theorem_prop("nat_le_zero_right")
}

pub fn nat_le_succ_zero_source_theorem() -> Prop {
    theorem_prop("nat_le_succ_zero")
}

pub fn nat_le_succ_succ_source_theorem() -> Prop {
    theorem_prop("nat_le_succ_succ")
}

pub fn nat_le_refl_source_theorem() -> Prop {
    theorem_prop("nat_le_refl")
}

pub fn nat_le_is_bool_source_theorem() -> Prop {
    theorem_prop("nat_le_is_bool")
}

pub fn nat_lt_zero_zero_source_theorem() -> Prop {
    theorem_prop("nat_lt_zero_zero")
}

pub fn nat_lt_zero_succ_source_theorem() -> Prop {
    theorem_prop("nat_lt_zero_succ")
}

pub fn nat_lt_succ_zero_source_theorem() -> Prop {
    theorem_prop("nat_lt_succ_zero")
}

pub fn nat_lt_succ_succ_source_theorem() -> Prop {
    theorem_prop("nat_lt_succ_succ")
}

pub fn nat_lt_irrefl_source_theorem() -> Prop {
    theorem_prop("nat_lt_irrefl")
}

pub fn nat_lt_is_bool_source_theorem() -> Prop {
    theorem_prop("nat_lt_is_bool")
}

pub fn nat_le_list_suffix_cons_source_theorem() -> Prop {
    theorem_prop("nat_le_list_suffix_cons")
}

pub fn nat_lt_list_suffix_cons_source_theorem() -> Prop {
    theorem_prop("nat_lt_list_suffix_cons")
}

pub fn nat_le_self_succ_source_theorem() -> Prop {
    theorem_prop("nat_le_self_succ")
}

pub fn nat_lt_self_succ_source_theorem() -> Prop {
    theorem_prop("nat_lt_self_succ")
}

pub fn nat_lt_implies_nat_le_source_theorem() -> Prop {
    theorem_prop("nat_lt_implies_nat_le")
}

pub fn nat_le_false_implies_nat_lt_right_left_source_theorem() -> Prop {
    theorem_prop("nat_le_false_implies_nat_lt_right_left")
}

pub fn nat_lt_false_implies_nat_le_right_left_source_theorem() -> Prop {
    theorem_prop("nat_lt_false_implies_nat_le_right_left")
}

pub fn nat_le_trans_source_theorem() -> Prop {
    theorem_prop("nat_le_trans")
}

pub fn nat_lt_trans_source_theorem() -> Prop {
    theorem_prop("nat_lt_trans")
}

pub fn nat_le_lt_trans_source_theorem() -> Prop {
    theorem_prop("nat_le_lt_trans")
}

pub fn nat_lt_le_trans_source_theorem() -> Prop {
    theorem_prop("nat_lt_le_trans")
}

pub fn nat_eq_symm_source_theorem() -> Prop {
    theorem_prop("nat_eq_symm")
}

pub fn nat_eq_trans_source_theorem() -> Prop {
    theorem_prop("nat_eq_trans")
}

pub fn nat_eq_sound_source_theorem() -> Prop {
    theorem_prop("nat_eq_sound")
}

pub fn nat_eq_false_implies_nat_lt_or_nat_lt_source_theorem() -> Prop {
    theorem_prop("nat_eq_false_implies_nat_lt_or_nat_lt")
}

pub fn nat_eq_implies_nat_le_left_right_source_theorem() -> Prop {
    theorem_prop("nat_eq_implies_nat_le_left_right")
}

pub fn nat_eq_implies_nat_le_right_left_source_theorem() -> Prop {
    theorem_prop("nat_eq_implies_nat_le_right_left")
}

pub fn nat_le_antisymm_source_theorem() -> Prop {
    theorem_prop("nat_le_antisymm")
}

pub fn nat_le_implies_nat_lt_cons_right_source_theorem() -> Prop {
    theorem_prop("nat_le_implies_nat_lt_cons_right")
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

pub fn nat_le_left_add_source_theorem() -> Prop {
    theorem_prop("nat_le_left_add")
}

pub fn nat_lt_left_add_succ_right_source_theorem() -> Prop {
    theorem_prop("nat_lt_left_add_succ_right")
}

pub fn nat_le_right_add_source_theorem() -> Prop {
    theorem_prop("nat_le_right_add")
}

pub fn nat_lt_nil_left_add_source_theorem() -> Prop {
    theorem_prop("nat_lt_nil_left_add")
}

pub fn nat_le_add_right_mono_source_theorem() -> Prop {
    theorem_prop("nat_le_add_right_mono")
}

pub fn nat_lt_add_right_mono_source_theorem() -> Prop {
    theorem_prop("nat_lt_add_right_mono")
}

pub fn nat_le_add_left_mono_source_theorem() -> Prop {
    theorem_prop("nat_le_add_left_mono")
}

pub fn nat_lt_add_left_mono_source_theorem() -> Prop {
    theorem_prop("nat_lt_add_left_mono")
}

pub fn nat_le_add_left_cancel_source_theorem() -> Prop {
    theorem_prop("nat_le_add_left_cancel")
}

pub fn nat_lt_add_left_cancel_source_theorem() -> Prop {
    theorem_prop("nat_lt_add_left_cancel")
}

pub fn nat_le_add_right_cancel_source_theorem() -> Prop {
    theorem_prop("nat_le_add_right_cancel")
}

pub fn nat_lt_add_right_cancel_source_theorem() -> Prop {
    theorem_prop("nat_lt_add_right_cancel")
}

pub fn add_succ_left_source_theorem() -> Prop {
    theorem_prop("add_succ_left")
}

pub fn pred_add_succ_left_source_theorem() -> Prop {
    theorem_prop("pred_add_succ_left")
}

pub fn is_zero_add_succ_left_source_theorem() -> Prop {
    theorem_prop("is_zero_add_succ_left")
}

pub fn add_cons_unit_right_source_theorem() -> Prop {
    theorem_prop("add_cons_unit_right")
}

pub fn add_succ_right_source_theorem() -> Prop {
    theorem_prop("add_succ_right")
}

pub fn pred_add_succ_right_source_theorem() -> Prop {
    theorem_prop("pred_add_succ_right")
}

pub fn is_zero_add_succ_right_source_theorem() -> Prop {
    theorem_prop("is_zero_add_succ_right")
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

pub fn sub_zero_right_source_theorem() -> Prop {
    theorem_prop("sub_zero_right")
}

pub fn sub_zero_left_source_theorem() -> Prop {
    theorem_prop("sub_zero_left")
}

pub fn sub_succ_succ_source_theorem() -> Prop {
    theorem_prop("sub_succ_succ")
}

pub fn sub_computes_to_list_source_theorem() -> Prop {
    theorem_prop("sub_computes_to_list")
}

pub fn sub_preserves_nat_value_source_theorem() -> Prop {
    theorem_prop("sub_preserves_nat_value")
}

pub fn add_sub_cancel_left_source_theorem() -> Prop {
    theorem_prop("add_sub_cancel_left")
}

pub fn add_sub_cancel_right_source_theorem() -> Prop {
    theorem_prop("add_sub_cancel_right")
}

pub fn sub_self_source_theorem() -> Prop {
    theorem_prop("sub_self")
}

pub fn nat_le_sub_left_source_theorem() -> Prop {
    theorem_prop("nat_le_sub_left")
}

pub fn nat_le_implies_sub_zero_source_theorem() -> Prop {
    theorem_prop("nat_le_implies_sub_zero")
}

pub fn nat_le_of_sub_zero_source_theorem() -> Prop {
    theorem_prop("nat_le_of_sub_zero")
}

pub fn nat_le_add_sub_cancel_source_theorem() -> Prop {
    theorem_prop("nat_le_add_sub_cancel")
}

pub fn nat_le_add_sub_cancel_right_source_theorem() -> Prop {
    theorem_prop("nat_le_add_sub_cancel_right")
}

pub fn nat_le_of_add_sub_cancel_source_theorem() -> Prop {
    theorem_prop("nat_le_of_add_sub_cancel")
}

pub fn nat_lt_right_left_implies_nat_lt_zero_sub_source_theorem() -> Prop {
    theorem_prop("nat_lt_right_left_implies_nat_lt_zero_sub")
}

pub fn nat_lt_zero_sub_implies_nat_lt_right_left_source_theorem() -> Prop {
    theorem_prop("nat_lt_zero_sub_implies_nat_lt_right_left")
}

pub fn mul_zero_left_source_theorem() -> Prop {
    theorem_prop("mul_zero_left")
}

pub fn is_zero_mul_zero_left_source_theorem() -> Prop {
    theorem_prop("is_zero_mul_zero_left")
}

pub fn mul_cons_source_theorem() -> Prop {
    theorem_prop("mul_cons")
}

pub fn mul_computes_to_list_source_theorem() -> Prop {
    theorem_prop("mul_computes_to_list")
}

pub fn nat_le_mul_right_mono_source_theorem() -> Prop {
    theorem_prop("nat_le_mul_right_mono")
}

pub fn nat_lt_mul_right_mono_source_theorem() -> Prop {
    theorem_prop("nat_lt_mul_right_mono")
}

pub fn nat_le_mul_left_mono_source_theorem() -> Prop {
    theorem_prop("nat_le_mul_left_mono")
}

pub fn nat_lt_mul_left_mono_source_theorem() -> Prop {
    theorem_prop("nat_lt_mul_left_mono")
}

pub fn mul_preserves_nat_value_source_theorem() -> Prop {
    theorem_prop("mul_preserves_nat_value")
}

pub fn mul_succ_left_source_theorem() -> Prop {
    theorem_prop("mul_succ_left")
}

pub fn is_zero_mul_succ_succ_source_theorem() -> Prop {
    theorem_prop("is_zero_mul_succ_succ")
}

pub fn pred_mul_succ_succ_source_theorem() -> Prop {
    theorem_prop("pred_mul_succ_succ")
}

pub fn mul_succ_right_source_theorem() -> Prop {
    theorem_prop("mul_succ_right")
}

pub fn mul_zero_right_source_theorem() -> Prop {
    theorem_prop("mul_zero_right")
}

pub fn is_zero_mul_zero_right_source_theorem() -> Prop {
    theorem_prop("is_zero_mul_zero_right")
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
        sub(),
        Computation::Ref(super::computation_name("sub").unwrap())
    );
    assert_eq!(
        mul(),
        Computation::Ref(super::computation_name("mul").unwrap())
    );
    assert_eq!(
        nat_eq(),
        Computation::Ref(super::computation_name("nat-eq").unwrap())
    );
    assert_eq!(
        nat_le(),
        Computation::Ref(super::computation_name("nat-le").unwrap())
    );
    assert_eq!(
        nat_lt(),
        Computation::Ref(super::computation_name("nat-lt").unwrap())
    );
}

#[test]
fn nat_theorem_statements_load_from_source() {
    let zero_result = theorem_symbol("zero_computes_to_list", "result");
    let is_zero_bool_nat = theorem_symbol("is_zero_is_bool", "nat");
    let pred_succ_nat = theorem_symbol("pred_succ", "nat");
    let pred_result = theorem_symbol("pred_computes_to_list", "result");
    let pred_nat = theorem_symbol("pred_computes_to_list", "nat");
    let nat_eq_refl_nat = theorem_symbol("nat_eq_refl", "nat");
    let nat_eq_is_bool_left = theorem_symbol("nat_eq_is_bool", "left");
    let nat_eq_is_bool_right = theorem_symbol("nat_eq_is_bool", "right");
    let nat_le_refl_nat = theorem_symbol("nat_le_refl", "nat");
    let nat_le_is_bool_left = theorem_symbol("nat_le_is_bool", "left");
    let nat_le_is_bool_right = theorem_symbol("nat_le_is_bool", "right");
    let nat_lt_succ_succ_left = theorem_symbol("nat_lt_succ_succ", "left");
    let nat_lt_succ_succ_right = theorem_symbol("nat_lt_succ_succ", "right");
    let nat_le_suffix_tail = theorem_symbol("nat_le_list_suffix_cons", "tail");
    let nat_le_suffix_head = theorem_symbol("nat_le_list_suffix_cons", "head");
    let nat_lt_suffix_tail = theorem_symbol("nat_lt_list_suffix_cons", "tail");
    let nat_lt_suffix_head = theorem_symbol("nat_lt_list_suffix_cons", "head");
    let nat_le_self_succ_nat = theorem_symbol("nat_le_self_succ", "nat");
    let nat_lt_self_succ_nat = theorem_symbol("nat_lt_self_succ", "nat");
    let nat_lt_implies_le_left = theorem_symbol("nat_lt_implies_nat_le", "left");
    let nat_lt_implies_le_right = theorem_symbol("nat_lt_implies_nat_le", "right");
    let nat_le_false_lt_left = theorem_symbol("nat_le_false_implies_nat_lt_right_left", "left");
    let nat_le_false_lt_right = theorem_symbol("nat_le_false_implies_nat_lt_right_left", "right");
    let nat_lt_false_le_left = theorem_symbol("nat_lt_false_implies_nat_le_right_left", "left");
    let nat_lt_false_le_right = theorem_symbol("nat_lt_false_implies_nat_le_right_left", "right");
    let nat_le_trans_left = theorem_symbol("nat_le_trans", "left");
    let nat_le_trans_middle = theorem_symbol("nat_le_trans", "middle");
    let nat_le_trans_right = theorem_symbol("nat_le_trans", "right");
    let nat_lt_trans_left = theorem_symbol("nat_lt_trans", "left");
    let nat_lt_trans_middle = theorem_symbol("nat_lt_trans", "middle");
    let nat_lt_trans_right = theorem_symbol("nat_lt_trans", "right");
    let nat_le_lt_trans_left = theorem_symbol("nat_le_lt_trans", "left");
    let nat_le_lt_trans_middle = theorem_symbol("nat_le_lt_trans", "middle");
    let nat_le_lt_trans_right = theorem_symbol("nat_le_lt_trans", "right");
    let nat_lt_le_trans_left = theorem_symbol("nat_lt_le_trans", "left");
    let nat_lt_le_trans_middle = theorem_symbol("nat_lt_le_trans", "middle");
    let nat_lt_le_trans_right = theorem_symbol("nat_lt_le_trans", "right");
    let nat_eq_symm_left = theorem_symbol("nat_eq_symm", "left");
    let nat_eq_symm_right = theorem_symbol("nat_eq_symm", "right");
    let nat_eq_trans_left = theorem_symbol("nat_eq_trans", "left");
    let nat_eq_trans_middle = theorem_symbol("nat_eq_trans", "middle");
    let nat_eq_trans_right = theorem_symbol("nat_eq_trans", "right");
    let nat_eq_sound_left = theorem_symbol("nat_eq_sound", "left");
    let nat_eq_sound_right = theorem_symbol("nat_eq_sound", "right");
    let nat_eq_false_lt_left = theorem_symbol("nat_eq_false_implies_nat_lt_or_nat_lt", "left");
    let nat_eq_false_lt_right = theorem_symbol("nat_eq_false_implies_nat_lt_or_nat_lt", "right");
    let nat_eq_le_lr_left = theorem_symbol("nat_eq_implies_nat_le_left_right", "left");
    let nat_eq_le_lr_right = theorem_symbol("nat_eq_implies_nat_le_left_right", "right");
    let nat_eq_le_rl_left = theorem_symbol("nat_eq_implies_nat_le_right_left", "left");
    let nat_eq_le_rl_right = theorem_symbol("nat_eq_implies_nat_le_right_left", "right");
    let nat_le_antisymm_left = theorem_symbol("nat_le_antisymm", "left");
    let nat_le_antisymm_right = theorem_symbol("nat_le_antisymm", "right");
    let nat_le_lt_cons_left = theorem_symbol("nat_le_implies_nat_lt_cons_right", "left");
    let nat_le_lt_cons_right = theorem_symbol("nat_le_implies_nat_lt_cons_right", "right");
    let nat_le_lt_cons_head = theorem_symbol("nat_le_implies_nat_lt_cons_right", "head");
    let add_zero_left_right = theorem_symbol("add_zero_left", "right");
    let add_zero_right_nat = theorem_symbol("add_zero_right", "nat");
    let nat_le_left_add_left = theorem_symbol("nat_le_left_add", "left");
    let nat_le_left_add_right = theorem_symbol("nat_le_left_add", "right");
    let nat_le_right_add_left = theorem_symbol("nat_le_right_add", "left");
    let nat_le_right_add_right = theorem_symbol("nat_le_right_add", "right");
    let nat_lt_nil_left_add_left = theorem_symbol("nat_lt_nil_left_add", "left");
    let nat_lt_nil_left_add_right = theorem_symbol("nat_lt_nil_left_add", "right");
    let nat_le_add_right_mono_left = theorem_symbol("nat_le_add_right_mono", "left");
    let nat_le_add_right_mono_right = theorem_symbol("nat_le_add_right_mono", "right");
    let nat_le_add_right_mono_suffix = theorem_symbol("nat_le_add_right_mono", "suffix");
    let nat_lt_add_right_mono_left = theorem_symbol("nat_lt_add_right_mono", "left");
    let nat_lt_add_right_mono_right = theorem_symbol("nat_lt_add_right_mono", "right");
    let nat_lt_add_right_mono_suffix = theorem_symbol("nat_lt_add_right_mono", "suffix");
    let nat_le_add_left_mono_left = theorem_symbol("nat_le_add_left_mono", "left");
    let nat_le_add_left_mono_right = theorem_symbol("nat_le_add_left_mono", "right");
    let nat_le_add_left_mono_prefix = theorem_symbol("nat_le_add_left_mono", "prefix");
    let nat_lt_add_left_mono_left = theorem_symbol("nat_lt_add_left_mono", "left");
    let nat_lt_add_left_mono_right = theorem_symbol("nat_lt_add_left_mono", "right");
    let nat_lt_add_left_mono_prefix = theorem_symbol("nat_lt_add_left_mono", "prefix");
    let nat_le_add_left_cancel_left = theorem_symbol("nat_le_add_left_cancel", "left");
    let nat_le_add_left_cancel_right = theorem_symbol("nat_le_add_left_cancel", "right");
    let nat_le_add_left_cancel_prefix = theorem_symbol("nat_le_add_left_cancel", "prefix");
    let nat_lt_add_left_cancel_left = theorem_symbol("nat_lt_add_left_cancel", "left");
    let nat_lt_add_left_cancel_right = theorem_symbol("nat_lt_add_left_cancel", "right");
    let nat_lt_add_left_cancel_prefix = theorem_symbol("nat_lt_add_left_cancel", "prefix");
    let nat_le_add_right_cancel_left = theorem_symbol("nat_le_add_right_cancel", "left");
    let nat_le_add_right_cancel_right = theorem_symbol("nat_le_add_right_cancel", "right");
    let nat_le_add_right_cancel_suffix = theorem_symbol("nat_le_add_right_cancel", "suffix");
    let nat_lt_add_right_cancel_left = theorem_symbol("nat_lt_add_right_cancel", "left");
    let nat_lt_add_right_cancel_right = theorem_symbol("nat_lt_add_right_cancel", "right");
    let nat_lt_add_right_cancel_suffix = theorem_symbol("nat_lt_add_right_cancel", "suffix");
    let sub_zero_right_left = theorem_symbol("sub_zero_right", "left");
    let sub_zero_left_right = theorem_symbol("sub_zero_left", "right");
    let sub_succ_succ_left = theorem_symbol("sub_succ_succ", "left");
    let sub_succ_succ_right = theorem_symbol("sub_succ_succ", "right");
    let sub_result = theorem_symbol("sub_computes_to_list", "result");
    let sub_left = theorem_symbol("sub_computes_to_list", "left");
    let sub_right = theorem_symbol("sub_computes_to_list", "right");
    let sub_preserves_nat_value_left = theorem_symbol("sub_preserves_nat_value", "left");
    let sub_preserves_nat_value_right = theorem_symbol("sub_preserves_nat_value", "right");
    let add_sub_cancel_left_left = theorem_symbol("add_sub_cancel_left", "left");
    let add_sub_cancel_left_right = theorem_symbol("add_sub_cancel_left", "right");
    let add_sub_cancel_right_left = theorem_symbol("add_sub_cancel_right", "left");
    let add_sub_cancel_right_right = theorem_symbol("add_sub_cancel_right", "right");
    let sub_self_nat = theorem_symbol("sub_self", "nat");
    let nat_le_sub_left_left = theorem_symbol("nat_le_sub_left", "left");
    let nat_le_sub_left_right = theorem_symbol("nat_le_sub_left", "right");
    let nat_le_implies_sub_zero_left = theorem_symbol("nat_le_implies_sub_zero", "left");
    let nat_le_implies_sub_zero_right = theorem_symbol("nat_le_implies_sub_zero", "right");
    let nat_le_of_sub_zero_left = theorem_symbol("nat_le_of_sub_zero", "left");
    let nat_le_of_sub_zero_right = theorem_symbol("nat_le_of_sub_zero", "right");
    let nat_le_add_sub_cancel_left = theorem_symbol("nat_le_add_sub_cancel", "left");
    let nat_le_add_sub_cancel_right = theorem_symbol("nat_le_add_sub_cancel", "right");
    let nat_le_add_sub_cancel_right_theorem_left =
        theorem_symbol("nat_le_add_sub_cancel_right", "left");
    let nat_le_add_sub_cancel_right_theorem_right =
        theorem_symbol("nat_le_add_sub_cancel_right", "right");
    let nat_le_of_add_sub_cancel_left = theorem_symbol("nat_le_of_add_sub_cancel", "left");
    let nat_le_of_add_sub_cancel_right = theorem_symbol("nat_le_of_add_sub_cancel", "right");
    let nat_lt_sub_positive_left =
        theorem_symbol("nat_lt_right_left_implies_nat_lt_zero_sub", "left");
    let nat_lt_sub_positive_right =
        theorem_symbol("nat_lt_right_left_implies_nat_lt_zero_sub", "right");
    let nat_lt_sub_positive_elim_left =
        theorem_symbol("nat_lt_zero_sub_implies_nat_lt_right_left", "left");
    let nat_lt_sub_positive_elim_right =
        theorem_symbol("nat_lt_zero_sub_implies_nat_lt_right_left", "right");
    let mul_result = theorem_symbol("mul_computes_to_list", "result");
    let mul_left = theorem_symbol("mul_computes_to_list", "left");
    let mul_right = theorem_symbol("mul_computes_to_list", "right");
    let nat_le_mul_right_mono_left = theorem_symbol("nat_le_mul_right_mono", "left");
    let nat_le_mul_right_mono_right = theorem_symbol("nat_le_mul_right_mono", "right");
    let nat_le_mul_right_mono_factor = theorem_symbol("nat_le_mul_right_mono", "factor");
    let nat_lt_mul_right_mono_left = theorem_symbol("nat_lt_mul_right_mono", "left");
    let nat_lt_mul_right_mono_right = theorem_symbol("nat_lt_mul_right_mono", "right");
    let nat_lt_mul_right_mono_factor = theorem_symbol("nat_lt_mul_right_mono", "factor");
    let nat_le_mul_left_mono_left = theorem_symbol("nat_le_mul_left_mono", "left");
    let nat_le_mul_left_mono_right = theorem_symbol("nat_le_mul_left_mono", "right");
    let nat_le_mul_left_mono_factor = theorem_symbol("nat_le_mul_left_mono", "factor");
    let nat_lt_mul_left_mono_left = theorem_symbol("nat_lt_mul_left_mono", "left");
    let nat_lt_mul_left_mono_right = theorem_symbol("nat_lt_mul_left_mono", "right");
    let nat_lt_mul_left_mono_factor = theorem_symbol("nat_lt_mul_left_mono", "factor");
    let mul_zero_right_nat = theorem_symbol("mul_zero_right", "nat");
    let mul_one_left_right = theorem_symbol("mul_one_left", "right");

    assert_eq!(
        zero_computes_to_list_source_theorem(),
        computes_to_list(zero_result, zero())
    );
    assert_eq!(zero_eq_nil_source_theorem(), computes_to(zero(), nil()));
    assert_eq!(
        zero_is_nat_value_source_theorem(),
        computes_to(is_nat_value_call(zero()), true_value())
    );
    assert_eq!(
        is_zero_is_bool_source_theorem(),
        crate::forall_where(
            is_zero_bool_nat,
            is_list(var(is_zero_bool_nat)),
            is_bool(is_zero_call(var(is_zero_bool_nat)))
        )
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
        nat_eq_refl_source_theorem(),
        crate::forall_where(
            nat_eq_refl_nat,
            is_list(var(nat_eq_refl_nat)),
            computes_to(
                nat_eq_call(var(nat_eq_refl_nat), var(nat_eq_refl_nat)),
                true_value()
            )
        )
    );
    assert_eq!(
        nat_eq_is_bool_source_theorem(),
        crate::forall_where(
            nat_eq_is_bool_left,
            is_list(var(nat_eq_is_bool_left)),
            crate::forall_where(
                nat_eq_is_bool_right,
                is_list(var(nat_eq_is_bool_right)),
                is_bool(nat_eq_call(
                    var(nat_eq_is_bool_left),
                    var(nat_eq_is_bool_right)
                ))
            )
        )
    );
    assert_eq!(
        nat_le_refl_source_theorem(),
        crate::forall_where(
            nat_le_refl_nat,
            is_list(var(nat_le_refl_nat)),
            computes_to(
                nat_le_call(var(nat_le_refl_nat), var(nat_le_refl_nat)),
                true_value()
            )
        )
    );
    assert_eq!(
        nat_le_is_bool_source_theorem(),
        crate::forall_where(
            nat_le_is_bool_left,
            is_list(var(nat_le_is_bool_left)),
            crate::forall_where(
                nat_le_is_bool_right,
                is_list(var(nat_le_is_bool_right)),
                is_bool(nat_le_call(
                    var(nat_le_is_bool_left),
                    var(nat_le_is_bool_right)
                ))
            )
        )
    );
    assert_eq!(
        nat_lt_succ_succ_source_theorem(),
        crate::forall_where(
            nat_lt_succ_succ_left,
            is_list(var(nat_lt_succ_succ_left)),
            crate::forall_where(
                nat_lt_succ_succ_right,
                is_list(var(nat_lt_succ_succ_right)),
                computes_to(
                    nat_lt_call(
                        succ_call(var(nat_lt_succ_succ_left)),
                        succ_call(var(nat_lt_succ_succ_right))
                    ),
                    nat_lt_call(var(nat_lt_succ_succ_left), var(nat_lt_succ_succ_right))
                )
            )
        )
    );
    assert_eq!(
        nat_le_list_suffix_cons_source_theorem(),
        crate::forall_where(
            nat_le_suffix_tail,
            is_list(var(nat_le_suffix_tail)),
            crate::forall_where(
                nat_le_suffix_head,
                is_value(var(nat_le_suffix_head)),
                computes_to(
                    nat_le_call(
                        var(nat_le_suffix_tail),
                        cons(var(nat_le_suffix_head), var(nat_le_suffix_tail))
                    ),
                    true_value()
                )
            )
        )
    );
    assert_eq!(
        nat_lt_list_suffix_cons_source_theorem(),
        crate::forall_where(
            nat_lt_suffix_tail,
            is_list(var(nat_lt_suffix_tail)),
            crate::forall_where(
                nat_lt_suffix_head,
                is_value(var(nat_lt_suffix_head)),
                computes_to(
                    nat_lt_call(
                        var(nat_lt_suffix_tail),
                        cons(var(nat_lt_suffix_head), var(nat_lt_suffix_tail))
                    ),
                    true_value()
                )
            )
        )
    );
    assert_eq!(
        nat_le_self_succ_source_theorem(),
        crate::forall_where(
            nat_le_self_succ_nat,
            is_list(var(nat_le_self_succ_nat)),
            computes_to(
                nat_le_call(
                    var(nat_le_self_succ_nat),
                    succ_call(var(nat_le_self_succ_nat))
                ),
                true_value()
            )
        )
    );
    assert_eq!(
        nat_lt_self_succ_source_theorem(),
        crate::forall_where(
            nat_lt_self_succ_nat,
            is_list(var(nat_lt_self_succ_nat)),
            computes_to(
                nat_lt_call(
                    var(nat_lt_self_succ_nat),
                    succ_call(var(nat_lt_self_succ_nat))
                ),
                true_value()
            )
        )
    );
    assert_eq!(
        nat_lt_implies_nat_le_source_theorem(),
        crate::forall_where(
            nat_lt_implies_le_left,
            is_list(var(nat_lt_implies_le_left)),
            crate::forall_where(
                nat_lt_implies_le_right,
                is_list(var(nat_lt_implies_le_right)),
                implies(
                    computes_to(
                        nat_lt_call(var(nat_lt_implies_le_left), var(nat_lt_implies_le_right)),
                        true_value()
                    ),
                    computes_to(
                        nat_le_call(var(nat_lt_implies_le_left), var(nat_lt_implies_le_right)),
                        true_value()
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_le_false_implies_nat_lt_right_left_source_theorem(),
        crate::forall_where(
            nat_le_false_lt_left,
            is_list(var(nat_le_false_lt_left)),
            crate::forall_where(
                nat_le_false_lt_right,
                is_list(var(nat_le_false_lt_right)),
                implies(
                    computes_to(
                        nat_le_call(var(nat_le_false_lt_left), var(nat_le_false_lt_right)),
                        false_value()
                    ),
                    computes_to(
                        nat_lt_call(var(nat_le_false_lt_right), var(nat_le_false_lt_left)),
                        true_value()
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_lt_false_implies_nat_le_right_left_source_theorem(),
        crate::forall_where(
            nat_lt_false_le_left,
            is_list(var(nat_lt_false_le_left)),
            crate::forall_where(
                nat_lt_false_le_right,
                is_list(var(nat_lt_false_le_right)),
                implies(
                    computes_to(
                        nat_lt_call(var(nat_lt_false_le_left), var(nat_lt_false_le_right)),
                        false_value()
                    ),
                    computes_to(
                        nat_le_call(var(nat_lt_false_le_right), var(nat_lt_false_le_left)),
                        true_value()
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_le_trans_source_theorem(),
        crate::forall_where(
            nat_le_trans_left,
            is_list(var(nat_le_trans_left)),
            crate::forall_where(
                nat_le_trans_middle,
                is_list(var(nat_le_trans_middle)),
                crate::forall_where(
                    nat_le_trans_right,
                    is_list(var(nat_le_trans_right)),
                    implies(
                        computes_to(
                            nat_le_call(var(nat_le_trans_left), var(nat_le_trans_middle)),
                            true_value()
                        ),
                        implies(
                            computes_to(
                                nat_le_call(var(nat_le_trans_middle), var(nat_le_trans_right)),
                                true_value()
                            ),
                            computes_to(
                                nat_le_call(var(nat_le_trans_left), var(nat_le_trans_right)),
                                true_value()
                            )
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_lt_trans_source_theorem(),
        crate::forall_where(
            nat_lt_trans_left,
            is_list(var(nat_lt_trans_left)),
            crate::forall_where(
                nat_lt_trans_middle,
                is_list(var(nat_lt_trans_middle)),
                crate::forall_where(
                    nat_lt_trans_right,
                    is_list(var(nat_lt_trans_right)),
                    implies(
                        computes_to(
                            nat_lt_call(var(nat_lt_trans_left), var(nat_lt_trans_middle)),
                            true_value()
                        ),
                        implies(
                            computes_to(
                                nat_lt_call(var(nat_lt_trans_middle), var(nat_lt_trans_right)),
                                true_value()
                            ),
                            computes_to(
                                nat_lt_call(var(nat_lt_trans_left), var(nat_lt_trans_right)),
                                true_value()
                            )
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_le_lt_trans_source_theorem(),
        crate::forall_where(
            nat_le_lt_trans_left,
            is_list(var(nat_le_lt_trans_left)),
            crate::forall_where(
                nat_le_lt_trans_middle,
                is_list(var(nat_le_lt_trans_middle)),
                crate::forall_where(
                    nat_le_lt_trans_right,
                    is_list(var(nat_le_lt_trans_right)),
                    implies(
                        computes_to(
                            nat_le_call(var(nat_le_lt_trans_left), var(nat_le_lt_trans_middle)),
                            true_value()
                        ),
                        implies(
                            computes_to(
                                nat_lt_call(
                                    var(nat_le_lt_trans_middle),
                                    var(nat_le_lt_trans_right)
                                ),
                                true_value()
                            ),
                            computes_to(
                                nat_lt_call(var(nat_le_lt_trans_left), var(nat_le_lt_trans_right)),
                                true_value()
                            )
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_lt_le_trans_source_theorem(),
        crate::forall_where(
            nat_lt_le_trans_left,
            is_list(var(nat_lt_le_trans_left)),
            crate::forall_where(
                nat_lt_le_trans_middle,
                is_list(var(nat_lt_le_trans_middle)),
                crate::forall_where(
                    nat_lt_le_trans_right,
                    is_list(var(nat_lt_le_trans_right)),
                    implies(
                        computes_to(
                            nat_lt_call(var(nat_lt_le_trans_left), var(nat_lt_le_trans_middle)),
                            true_value()
                        ),
                        implies(
                            computes_to(
                                nat_le_call(
                                    var(nat_lt_le_trans_middle),
                                    var(nat_lt_le_trans_right)
                                ),
                                true_value()
                            ),
                            computes_to(
                                nat_lt_call(var(nat_lt_le_trans_left), var(nat_lt_le_trans_right)),
                                true_value()
                            )
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_eq_symm_source_theorem(),
        crate::forall_where(
            nat_eq_symm_left,
            is_list(var(nat_eq_symm_left)),
            crate::forall_where(
                nat_eq_symm_right,
                is_list(var(nat_eq_symm_right)),
                computes_to(
                    nat_eq_call(var(nat_eq_symm_left), var(nat_eq_symm_right)),
                    nat_eq_call(var(nat_eq_symm_right), var(nat_eq_symm_left))
                )
            )
        )
    );
    assert_eq!(
        nat_eq_trans_source_theorem(),
        crate::forall_where(
            nat_eq_trans_left,
            is_list(var(nat_eq_trans_left)),
            crate::forall_where(
                nat_eq_trans_middle,
                is_list(var(nat_eq_trans_middle)),
                crate::forall_where(
                    nat_eq_trans_right,
                    is_list(var(nat_eq_trans_right)),
                    implies(
                        computes_to(
                            nat_eq_call(var(nat_eq_trans_left), var(nat_eq_trans_middle)),
                            true_value()
                        ),
                        implies(
                            computes_to(
                                nat_eq_call(var(nat_eq_trans_middle), var(nat_eq_trans_right)),
                                true_value()
                            ),
                            computes_to(
                                nat_eq_call(var(nat_eq_trans_left), var(nat_eq_trans_right)),
                                true_value()
                            )
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_eq_sound_source_theorem(),
        crate::forall_where(
            nat_eq_sound_left,
            is_list(var(nat_eq_sound_left)),
            crate::forall_where(
                nat_eq_sound_right,
                is_list(var(nat_eq_sound_right)),
                implies(
                    computes_to(is_nat_value_call(var(nat_eq_sound_left)), true_value()),
                    implies(
                        computes_to(is_nat_value_call(var(nat_eq_sound_right)), true_value()),
                        implies(
                            computes_to(
                                nat_eq_call(var(nat_eq_sound_left), var(nat_eq_sound_right)),
                                true_value()
                            ),
                            computes_to(var(nat_eq_sound_left), var(nat_eq_sound_right))
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_eq_false_implies_nat_lt_or_nat_lt_source_theorem(),
        crate::forall_where(
            nat_eq_false_lt_left,
            is_list(var(nat_eq_false_lt_left)),
            crate::forall_where(
                nat_eq_false_lt_right,
                is_list(var(nat_eq_false_lt_right)),
                implies(
                    computes_to(
                        nat_eq_call(var(nat_eq_false_lt_left), var(nat_eq_false_lt_right)),
                        false_value()
                    ),
                    or(
                        computes_to(
                            nat_lt_call(var(nat_eq_false_lt_left), var(nat_eq_false_lt_right)),
                            true_value()
                        ),
                        computes_to(
                            nat_lt_call(var(nat_eq_false_lt_right), var(nat_eq_false_lt_left)),
                            true_value()
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_eq_implies_nat_le_left_right_source_theorem(),
        crate::forall_where(
            nat_eq_le_lr_left,
            is_list(var(nat_eq_le_lr_left)),
            crate::forall_where(
                nat_eq_le_lr_right,
                is_list(var(nat_eq_le_lr_right)),
                implies(
                    computes_to(
                        nat_eq_call(var(nat_eq_le_lr_left), var(nat_eq_le_lr_right)),
                        true_value()
                    ),
                    computes_to(
                        nat_le_call(var(nat_eq_le_lr_left), var(nat_eq_le_lr_right)),
                        true_value()
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_eq_implies_nat_le_right_left_source_theorem(),
        crate::forall_where(
            nat_eq_le_rl_left,
            is_list(var(nat_eq_le_rl_left)),
            crate::forall_where(
                nat_eq_le_rl_right,
                is_list(var(nat_eq_le_rl_right)),
                implies(
                    computes_to(
                        nat_eq_call(var(nat_eq_le_rl_left), var(nat_eq_le_rl_right)),
                        true_value()
                    ),
                    computes_to(
                        nat_le_call(var(nat_eq_le_rl_right), var(nat_eq_le_rl_left)),
                        true_value()
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_le_antisymm_source_theorem(),
        crate::forall_where(
            nat_le_antisymm_left,
            is_list(var(nat_le_antisymm_left)),
            crate::forall_where(
                nat_le_antisymm_right,
                is_list(var(nat_le_antisymm_right)),
                implies(
                    computes_to(
                        nat_le_call(var(nat_le_antisymm_left), var(nat_le_antisymm_right)),
                        true_value()
                    ),
                    implies(
                        computes_to(
                            nat_le_call(var(nat_le_antisymm_right), var(nat_le_antisymm_left)),
                            true_value()
                        ),
                        computes_to(
                            nat_eq_call(var(nat_le_antisymm_left), var(nat_le_antisymm_right)),
                            true_value()
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_le_implies_nat_lt_cons_right_source_theorem(),
        crate::forall_where(
            nat_le_lt_cons_left,
            is_list(var(nat_le_lt_cons_left)),
            crate::forall_where(
                nat_le_lt_cons_right,
                is_list(var(nat_le_lt_cons_right)),
                crate::forall_where(
                    nat_le_lt_cons_head,
                    is_value(var(nat_le_lt_cons_head)),
                    implies(
                        computes_to(
                            nat_le_call(var(nat_le_lt_cons_left), var(nat_le_lt_cons_right)),
                            true_value()
                        ),
                        computes_to(
                            nat_lt_call(
                                var(nat_le_lt_cons_left),
                                cons(var(nat_le_lt_cons_head), var(nat_le_lt_cons_right))
                            ),
                            true_value()
                        )
                    )
                )
            )
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
        nat_le_left_add_source_theorem(),
        crate::forall_where(
            nat_le_left_add_left,
            is_list(var(nat_le_left_add_left)),
            crate::forall_where(
                nat_le_left_add_right,
                is_list(var(nat_le_left_add_right)),
                computes_to(
                    nat_le_call(
                        var(nat_le_left_add_left),
                        add_call(var(nat_le_left_add_left), var(nat_le_left_add_right))
                    ),
                    true_value()
                )
            )
        )
    );
    assert_eq!(
        nat_le_right_add_source_theorem(),
        crate::forall_where(
            nat_le_right_add_left,
            is_list(var(nat_le_right_add_left)),
            crate::forall_where(
                nat_le_right_add_right,
                is_list(var(nat_le_right_add_right)),
                computes_to(
                    nat_le_call(
                        var(nat_le_right_add_right),
                        add_call(var(nat_le_right_add_left), var(nat_le_right_add_right))
                    ),
                    true_value()
                )
            )
        )
    );
    assert_eq!(
        nat_lt_nil_left_add_source_theorem(),
        crate::forall_where(
            nat_lt_nil_left_add_left,
            is_list(var(nat_lt_nil_left_add_left)),
            crate::forall_where(
                nat_lt_nil_left_add_right,
                is_list(var(nat_lt_nil_left_add_right)),
                implies(
                    computes_to(
                        nat_lt_call(nil(), var(nat_lt_nil_left_add_left)),
                        true_value()
                    ),
                    computes_to(
                        nat_lt_call(
                            nil(),
                            add_call(
                                var(nat_lt_nil_left_add_left),
                                var(nat_lt_nil_left_add_right)
                            )
                        ),
                        true_value()
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_le_add_right_mono_source_theorem(),
        crate::forall_where(
            nat_le_add_right_mono_left,
            is_list(var(nat_le_add_right_mono_left)),
            crate::forall_where(
                nat_le_add_right_mono_right,
                is_list(var(nat_le_add_right_mono_right)),
                crate::forall_where(
                    nat_le_add_right_mono_suffix,
                    is_list(var(nat_le_add_right_mono_suffix)),
                    implies(
                        computes_to(
                            nat_le_call(
                                var(nat_le_add_right_mono_left),
                                var(nat_le_add_right_mono_right)
                            ),
                            true_value()
                        ),
                        computes_to(
                            nat_le_call(
                                add_call(
                                    var(nat_le_add_right_mono_left),
                                    var(nat_le_add_right_mono_suffix)
                                ),
                                add_call(
                                    var(nat_le_add_right_mono_right),
                                    var(nat_le_add_right_mono_suffix)
                                )
                            ),
                            true_value()
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_lt_add_right_mono_source_theorem(),
        crate::forall_where(
            nat_lt_add_right_mono_left,
            is_list(var(nat_lt_add_right_mono_left)),
            crate::forall_where(
                nat_lt_add_right_mono_right,
                is_list(var(nat_lt_add_right_mono_right)),
                crate::forall_where(
                    nat_lt_add_right_mono_suffix,
                    is_list(var(nat_lt_add_right_mono_suffix)),
                    implies(
                        computes_to(
                            nat_lt_call(
                                var(nat_lt_add_right_mono_left),
                                var(nat_lt_add_right_mono_right)
                            ),
                            true_value()
                        ),
                        computes_to(
                            nat_lt_call(
                                add_call(
                                    var(nat_lt_add_right_mono_left),
                                    var(nat_lt_add_right_mono_suffix)
                                ),
                                add_call(
                                    var(nat_lt_add_right_mono_right),
                                    var(nat_lt_add_right_mono_suffix)
                                )
                            ),
                            true_value()
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_le_add_left_mono_source_theorem(),
        crate::forall_where(
            nat_le_add_left_mono_left,
            is_list(var(nat_le_add_left_mono_left)),
            crate::forall_where(
                nat_le_add_left_mono_right,
                is_list(var(nat_le_add_left_mono_right)),
                crate::forall_where(
                    nat_le_add_left_mono_prefix,
                    is_list(var(nat_le_add_left_mono_prefix)),
                    implies(
                        computes_to(
                            nat_le_call(
                                var(nat_le_add_left_mono_left),
                                var(nat_le_add_left_mono_right)
                            ),
                            true_value()
                        ),
                        computes_to(
                            nat_le_call(
                                add_call(
                                    var(nat_le_add_left_mono_prefix),
                                    var(nat_le_add_left_mono_left)
                                ),
                                add_call(
                                    var(nat_le_add_left_mono_prefix),
                                    var(nat_le_add_left_mono_right)
                                )
                            ),
                            true_value()
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_lt_add_left_mono_source_theorem(),
        crate::forall_where(
            nat_lt_add_left_mono_left,
            is_list(var(nat_lt_add_left_mono_left)),
            crate::forall_where(
                nat_lt_add_left_mono_right,
                is_list(var(nat_lt_add_left_mono_right)),
                crate::forall_where(
                    nat_lt_add_left_mono_prefix,
                    is_list(var(nat_lt_add_left_mono_prefix)),
                    implies(
                        computes_to(
                            nat_lt_call(
                                var(nat_lt_add_left_mono_left),
                                var(nat_lt_add_left_mono_right)
                            ),
                            true_value()
                        ),
                        computes_to(
                            nat_lt_call(
                                add_call(
                                    var(nat_lt_add_left_mono_prefix),
                                    var(nat_lt_add_left_mono_left)
                                ),
                                add_call(
                                    var(nat_lt_add_left_mono_prefix),
                                    var(nat_lt_add_left_mono_right)
                                )
                            ),
                            true_value()
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_le_add_left_cancel_source_theorem(),
        crate::forall_where(
            nat_le_add_left_cancel_left,
            is_list(var(nat_le_add_left_cancel_left)),
            crate::forall_where(
                nat_le_add_left_cancel_right,
                is_list(var(nat_le_add_left_cancel_right)),
                crate::forall_where(
                    nat_le_add_left_cancel_prefix,
                    is_list(var(nat_le_add_left_cancel_prefix)),
                    implies(
                        computes_to(
                            nat_le_call(
                                add_call(
                                    var(nat_le_add_left_cancel_prefix),
                                    var(nat_le_add_left_cancel_left)
                                ),
                                add_call(
                                    var(nat_le_add_left_cancel_prefix),
                                    var(nat_le_add_left_cancel_right)
                                )
                            ),
                            true_value()
                        ),
                        computes_to(
                            nat_le_call(
                                var(nat_le_add_left_cancel_left),
                                var(nat_le_add_left_cancel_right)
                            ),
                            true_value()
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_lt_add_left_cancel_source_theorem(),
        crate::forall_where(
            nat_lt_add_left_cancel_left,
            is_list(var(nat_lt_add_left_cancel_left)),
            crate::forall_where(
                nat_lt_add_left_cancel_right,
                is_list(var(nat_lt_add_left_cancel_right)),
                crate::forall_where(
                    nat_lt_add_left_cancel_prefix,
                    is_list(var(nat_lt_add_left_cancel_prefix)),
                    implies(
                        computes_to(
                            nat_lt_call(
                                add_call(
                                    var(nat_lt_add_left_cancel_prefix),
                                    var(nat_lt_add_left_cancel_left)
                                ),
                                add_call(
                                    var(nat_lt_add_left_cancel_prefix),
                                    var(nat_lt_add_left_cancel_right)
                                )
                            ),
                            true_value()
                        ),
                        computes_to(
                            nat_lt_call(
                                var(nat_lt_add_left_cancel_left),
                                var(nat_lt_add_left_cancel_right)
                            ),
                            true_value()
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_le_add_right_cancel_source_theorem(),
        crate::forall_where(
            nat_le_add_right_cancel_left,
            is_list(var(nat_le_add_right_cancel_left)),
            crate::forall_where(
                nat_le_add_right_cancel_right,
                is_list(var(nat_le_add_right_cancel_right)),
                crate::forall_where(
                    nat_le_add_right_cancel_suffix,
                    is_list(var(nat_le_add_right_cancel_suffix)),
                    implies(
                        computes_to(
                            is_nat_value_call(var(nat_le_add_right_cancel_left)),
                            true_value()
                        ),
                        implies(
                            computes_to(
                                is_nat_value_call(var(nat_le_add_right_cancel_right)),
                                true_value()
                            ),
                            implies(
                                computes_to(
                                    is_nat_value_call(var(nat_le_add_right_cancel_suffix)),
                                    true_value()
                                ),
                                implies(
                                    computes_to(
                                        nat_le_call(
                                            add_call(
                                                var(nat_le_add_right_cancel_left),
                                                var(nat_le_add_right_cancel_suffix)
                                            ),
                                            add_call(
                                                var(nat_le_add_right_cancel_right),
                                                var(nat_le_add_right_cancel_suffix)
                                            )
                                        ),
                                        true_value()
                                    ),
                                    computes_to(
                                        nat_le_call(
                                            var(nat_le_add_right_cancel_left),
                                            var(nat_le_add_right_cancel_right)
                                        ),
                                        true_value()
                                    )
                                )
                            )
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_lt_add_right_cancel_source_theorem(),
        crate::forall_where(
            nat_lt_add_right_cancel_left,
            is_list(var(nat_lt_add_right_cancel_left)),
            crate::forall_where(
                nat_lt_add_right_cancel_right,
                is_list(var(nat_lt_add_right_cancel_right)),
                crate::forall_where(
                    nat_lt_add_right_cancel_suffix,
                    is_list(var(nat_lt_add_right_cancel_suffix)),
                    implies(
                        computes_to(
                            is_nat_value_call(var(nat_lt_add_right_cancel_left)),
                            true_value()
                        ),
                        implies(
                            computes_to(
                                is_nat_value_call(var(nat_lt_add_right_cancel_right)),
                                true_value()
                            ),
                            implies(
                                computes_to(
                                    is_nat_value_call(var(nat_lt_add_right_cancel_suffix)),
                                    true_value()
                                ),
                                implies(
                                    computes_to(
                                        nat_lt_call(
                                            add_call(
                                                var(nat_lt_add_right_cancel_left),
                                                var(nat_lt_add_right_cancel_suffix)
                                            ),
                                            add_call(
                                                var(nat_lt_add_right_cancel_right),
                                                var(nat_lt_add_right_cancel_suffix)
                                            )
                                        ),
                                        true_value()
                                    ),
                                    computes_to(
                                        nat_lt_call(
                                            var(nat_lt_add_right_cancel_left),
                                            var(nat_lt_add_right_cancel_right)
                                        ),
                                        true_value()
                                    )
                                )
                            )
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        sub_zero_right_source_theorem(),
        crate::forall_where(
            sub_zero_right_left,
            is_list(var(sub_zero_right_left)),
            computes_to(
                sub_call(var(sub_zero_right_left), zero()),
                var(sub_zero_right_left)
            )
        )
    );
    assert_eq!(
        sub_zero_left_source_theorem(),
        crate::forall_where(
            sub_zero_left_right,
            is_list(var(sub_zero_left_right)),
            computes_to(sub_call(zero(), var(sub_zero_left_right)), zero())
        )
    );
    assert_eq!(
        sub_succ_succ_source_theorem(),
        crate::forall_where(
            sub_succ_succ_left,
            is_list(var(sub_succ_succ_left)),
            crate::forall_where(
                sub_succ_succ_right,
                is_list(var(sub_succ_succ_right)),
                computes_to(
                    sub_call(
                        succ_call(var(sub_succ_succ_left)),
                        succ_call(var(sub_succ_succ_right))
                    ),
                    sub_call(var(sub_succ_succ_left), var(sub_succ_succ_right))
                )
            )
        )
    );
    assert_eq!(
        sub_computes_to_list_source_theorem(),
        crate::forall_where(
            sub_left,
            is_list(var(sub_left)),
            crate::forall_where(
                sub_right,
                is_list(var(sub_right)),
                computes_to_list(sub_result, sub_call(var(sub_left), var(sub_right)))
            )
        )
    );
    assert_eq!(
        sub_preserves_nat_value_source_theorem(),
        crate::forall_where(
            sub_preserves_nat_value_left,
            is_list(var(sub_preserves_nat_value_left)),
            crate::forall_where(
                sub_preserves_nat_value_right,
                is_list(var(sub_preserves_nat_value_right)),
                implies(
                    computes_to(
                        is_nat_value_call(var(sub_preserves_nat_value_left)),
                        true_value()
                    ),
                    implies(
                        computes_to(
                            is_nat_value_call(var(sub_preserves_nat_value_right)),
                            true_value()
                        ),
                        computes_to(
                            is_nat_value_call(sub_call(
                                var(sub_preserves_nat_value_left),
                                var(sub_preserves_nat_value_right)
                            )),
                            true_value()
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        add_sub_cancel_left_source_theorem(),
        crate::forall_where(
            add_sub_cancel_left_left,
            is_list(var(add_sub_cancel_left_left)),
            crate::forall_where(
                add_sub_cancel_left_right,
                is_list(var(add_sub_cancel_left_right)),
                computes_to(
                    sub_call(
                        add_call(
                            var(add_sub_cancel_left_left),
                            var(add_sub_cancel_left_right)
                        ),
                        var(add_sub_cancel_left_left)
                    ),
                    var(add_sub_cancel_left_right)
                )
            )
        )
    );
    assert_eq!(
        add_sub_cancel_right_source_theorem(),
        crate::forall_where(
            add_sub_cancel_right_left,
            is_list(var(add_sub_cancel_right_left)),
            crate::forall_where(
                add_sub_cancel_right_right,
                is_list(var(add_sub_cancel_right_right)),
                implies(
                    computes_to(
                        is_nat_value_call(var(add_sub_cancel_right_left)),
                        true_value()
                    ),
                    implies(
                        computes_to(
                            is_nat_value_call(var(add_sub_cancel_right_right)),
                            true_value()
                        ),
                        computes_to(
                            sub_call(
                                add_call(
                                    var(add_sub_cancel_right_left),
                                    var(add_sub_cancel_right_right)
                                ),
                                var(add_sub_cancel_right_right)
                            ),
                            var(add_sub_cancel_right_left)
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        sub_self_source_theorem(),
        crate::forall_where(
            sub_self_nat,
            is_list(var(sub_self_nat)),
            computes_to(sub_call(var(sub_self_nat), var(sub_self_nat)), zero())
        )
    );
    assert_eq!(
        nat_le_sub_left_source_theorem(),
        crate::forall_where(
            nat_le_sub_left_left,
            is_list(var(nat_le_sub_left_left)),
            crate::forall_where(
                nat_le_sub_left_right,
                is_list(var(nat_le_sub_left_right)),
                computes_to(
                    nat_le_call(
                        sub_call(var(nat_le_sub_left_left), var(nat_le_sub_left_right)),
                        var(nat_le_sub_left_left)
                    ),
                    true_value()
                )
            )
        )
    );
    assert_eq!(
        nat_le_implies_sub_zero_source_theorem(),
        crate::forall_where(
            nat_le_implies_sub_zero_left,
            is_list(var(nat_le_implies_sub_zero_left)),
            crate::forall_where(
                nat_le_implies_sub_zero_right,
                is_list(var(nat_le_implies_sub_zero_right)),
                implies(
                    computes_to(
                        nat_le_call(
                            var(nat_le_implies_sub_zero_left),
                            var(nat_le_implies_sub_zero_right)
                        ),
                        true_value()
                    ),
                    computes_to(
                        sub_call(
                            var(nat_le_implies_sub_zero_left),
                            var(nat_le_implies_sub_zero_right)
                        ),
                        zero()
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_le_of_sub_zero_source_theorem(),
        crate::forall_where(
            nat_le_of_sub_zero_left,
            is_list(var(nat_le_of_sub_zero_left)),
            crate::forall_where(
                nat_le_of_sub_zero_right,
                is_list(var(nat_le_of_sub_zero_right)),
                implies(
                    computes_to(
                        sub_call(var(nat_le_of_sub_zero_left), var(nat_le_of_sub_zero_right)),
                        zero()
                    ),
                    computes_to(
                        nat_le_call(var(nat_le_of_sub_zero_left), var(nat_le_of_sub_zero_right)),
                        true_value()
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_le_add_sub_cancel_source_theorem(),
        crate::forall_where(
            nat_le_add_sub_cancel_left,
            is_list(var(nat_le_add_sub_cancel_left)),
            crate::forall_where(
                nat_le_add_sub_cancel_right,
                is_list(var(nat_le_add_sub_cancel_right)),
                implies(
                    computes_to(
                        is_nat_value_call(var(nat_le_add_sub_cancel_left)),
                        true_value()
                    ),
                    implies(
                        computes_to(
                            is_nat_value_call(var(nat_le_add_sub_cancel_right)),
                            true_value()
                        ),
                        implies(
                            computes_to(
                                nat_le_call(
                                    var(nat_le_add_sub_cancel_right),
                                    var(nat_le_add_sub_cancel_left)
                                ),
                                true_value()
                            ),
                            computes_to(
                                add_call(
                                    var(nat_le_add_sub_cancel_right),
                                    sub_call(
                                        var(nat_le_add_sub_cancel_left),
                                        var(nat_le_add_sub_cancel_right)
                                    )
                                ),
                                var(nat_le_add_sub_cancel_left)
                            )
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_le_add_sub_cancel_right_source_theorem(),
        crate::forall_where(
            nat_le_add_sub_cancel_right_theorem_left,
            is_list(var(nat_le_add_sub_cancel_right_theorem_left)),
            crate::forall_where(
                nat_le_add_sub_cancel_right_theorem_right,
                is_list(var(nat_le_add_sub_cancel_right_theorem_right)),
                implies(
                    computes_to(
                        is_nat_value_call(var(nat_le_add_sub_cancel_right_theorem_left)),
                        true_value()
                    ),
                    implies(
                        computes_to(
                            is_nat_value_call(var(nat_le_add_sub_cancel_right_theorem_right)),
                            true_value()
                        ),
                        implies(
                            computes_to(
                                nat_le_call(
                                    var(nat_le_add_sub_cancel_right_theorem_right),
                                    var(nat_le_add_sub_cancel_right_theorem_left)
                                ),
                                true_value()
                            ),
                            computes_to(
                                add_call(
                                    sub_call(
                                        var(nat_le_add_sub_cancel_right_theorem_left),
                                        var(nat_le_add_sub_cancel_right_theorem_right)
                                    ),
                                    var(nat_le_add_sub_cancel_right_theorem_right)
                                ),
                                var(nat_le_add_sub_cancel_right_theorem_left)
                            )
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_le_of_add_sub_cancel_source_theorem(),
        crate::forall_where(
            nat_le_of_add_sub_cancel_left,
            is_list(var(nat_le_of_add_sub_cancel_left)),
            crate::forall_where(
                nat_le_of_add_sub_cancel_right,
                is_list(var(nat_le_of_add_sub_cancel_right)),
                implies(
                    computes_to(
                        add_call(
                            var(nat_le_of_add_sub_cancel_right),
                            sub_call(
                                var(nat_le_of_add_sub_cancel_left),
                                var(nat_le_of_add_sub_cancel_right)
                            )
                        ),
                        var(nat_le_of_add_sub_cancel_left)
                    ),
                    computes_to(
                        nat_le_call(
                            var(nat_le_of_add_sub_cancel_right),
                            var(nat_le_of_add_sub_cancel_left)
                        ),
                        true_value()
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_lt_right_left_implies_nat_lt_zero_sub_source_theorem(),
        crate::forall_where(
            nat_lt_sub_positive_left,
            is_list(var(nat_lt_sub_positive_left)),
            crate::forall_where(
                nat_lt_sub_positive_right,
                is_list(var(nat_lt_sub_positive_right)),
                implies(
                    computes_to(
                        nat_lt_call(
                            var(nat_lt_sub_positive_right),
                            var(nat_lt_sub_positive_left)
                        ),
                        true_value()
                    ),
                    computes_to(
                        nat_lt_call(
                            zero(),
                            sub_call(
                                var(nat_lt_sub_positive_left),
                                var(nat_lt_sub_positive_right)
                            )
                        ),
                        true_value()
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_lt_zero_sub_implies_nat_lt_right_left_source_theorem(),
        crate::forall_where(
            nat_lt_sub_positive_elim_left,
            is_list(var(nat_lt_sub_positive_elim_left)),
            crate::forall_where(
                nat_lt_sub_positive_elim_right,
                is_list(var(nat_lt_sub_positive_elim_right)),
                implies(
                    computes_to(
                        nat_lt_call(
                            zero(),
                            sub_call(
                                var(nat_lt_sub_positive_elim_left),
                                var(nat_lt_sub_positive_elim_right)
                            )
                        ),
                        true_value()
                    ),
                    computes_to(
                        nat_lt_call(
                            var(nat_lt_sub_positive_elim_right),
                            var(nat_lt_sub_positive_elim_left)
                        ),
                        true_value()
                    )
                )
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
        nat_le_mul_right_mono_source_theorem(),
        crate::forall_where(
            nat_le_mul_right_mono_left,
            is_list(var(nat_le_mul_right_mono_left)),
            crate::forall_where(
                nat_le_mul_right_mono_right,
                is_list(var(nat_le_mul_right_mono_right)),
                crate::forall_where(
                    nat_le_mul_right_mono_factor,
                    is_list(var(nat_le_mul_right_mono_factor)),
                    implies(
                        computes_to(
                            nat_le_call(
                                var(nat_le_mul_right_mono_left),
                                var(nat_le_mul_right_mono_right)
                            ),
                            true_value()
                        ),
                        computes_to(
                            nat_le_call(
                                mul_call(
                                    var(nat_le_mul_right_mono_left),
                                    var(nat_le_mul_right_mono_factor)
                                ),
                                mul_call(
                                    var(nat_le_mul_right_mono_right),
                                    var(nat_le_mul_right_mono_factor)
                                )
                            ),
                            true_value()
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_lt_mul_right_mono_source_theorem(),
        crate::forall_where(
            nat_lt_mul_right_mono_left,
            is_list(var(nat_lt_mul_right_mono_left)),
            crate::forall_where(
                nat_lt_mul_right_mono_right,
                is_list(var(nat_lt_mul_right_mono_right)),
                crate::forall_where(
                    nat_lt_mul_right_mono_factor,
                    is_list(var(nat_lt_mul_right_mono_factor)),
                    implies(
                        computes_to(
                            nat_lt_call(
                                var(nat_lt_mul_right_mono_left),
                                var(nat_lt_mul_right_mono_right)
                            ),
                            true_value()
                        ),
                        implies(
                            computes_to(
                                nat_lt_call(zero(), var(nat_lt_mul_right_mono_factor)),
                                true_value()
                            ),
                            computes_to(
                                nat_lt_call(
                                    mul_call(
                                        var(nat_lt_mul_right_mono_left),
                                        var(nat_lt_mul_right_mono_factor)
                                    ),
                                    mul_call(
                                        var(nat_lt_mul_right_mono_right),
                                        var(nat_lt_mul_right_mono_factor)
                                    )
                                ),
                                true_value()
                            )
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_le_mul_left_mono_source_theorem(),
        crate::forall_where(
            nat_le_mul_left_mono_left,
            is_list(var(nat_le_mul_left_mono_left)),
            crate::forall_where(
                nat_le_mul_left_mono_right,
                is_list(var(nat_le_mul_left_mono_right)),
                crate::forall_where(
                    nat_le_mul_left_mono_factor,
                    is_list(var(nat_le_mul_left_mono_factor)),
                    implies(
                        computes_to(
                            nat_le_call(
                                var(nat_le_mul_left_mono_left),
                                var(nat_le_mul_left_mono_right)
                            ),
                            true_value()
                        ),
                        computes_to(
                            nat_le_call(
                                mul_call(
                                    var(nat_le_mul_left_mono_factor),
                                    var(nat_le_mul_left_mono_left)
                                ),
                                mul_call(
                                    var(nat_le_mul_left_mono_factor),
                                    var(nat_le_mul_left_mono_right)
                                )
                            ),
                            true_value()
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_lt_mul_left_mono_source_theorem(),
        crate::forall_where(
            nat_lt_mul_left_mono_left,
            is_list(var(nat_lt_mul_left_mono_left)),
            crate::forall_where(
                nat_lt_mul_left_mono_right,
                is_list(var(nat_lt_mul_left_mono_right)),
                crate::forall_where(
                    nat_lt_mul_left_mono_factor,
                    is_list(var(nat_lt_mul_left_mono_factor)),
                    implies(
                        computes_to(
                            nat_lt_call(
                                var(nat_lt_mul_left_mono_left),
                                var(nat_lt_mul_left_mono_right)
                            ),
                            true_value()
                        ),
                        implies(
                            computes_to(
                                nat_lt_call(zero(), var(nat_lt_mul_left_mono_factor)),
                                true_value()
                            ),
                            computes_to(
                                nat_lt_call(
                                    mul_call(
                                        var(nat_lt_mul_left_mono_factor),
                                        var(nat_lt_mul_left_mono_left)
                                    ),
                                    mul_call(
                                        var(nat_lt_mul_left_mono_factor),
                                        var(nat_lt_mul_left_mono_right)
                                    )
                                ),
                                true_value()
                            )
                        )
                    )
                )
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

#[test]
fn checked_theory_contains_nat_theorems() {
    let theory = super::theory();

    assert_theory_has_theorem(&theory, "add_is_append", add_is_append_source_theorem());
    assert_theory_has_theorem(&theory, "zero_eq_nil", zero_eq_nil_source_theorem());
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
    assert_theory_has_theorem(&theory, "is_zero_is_bool", is_zero_is_bool_source_theorem());
    assert_theory_has_theorem(&theory, "pred_zero", pred_zero_source_theorem());
    assert_theory_has_theorem(&theory, "pred_succ", pred_succ_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "is_zero_pred_succ",
        is_zero_pred_succ_source_theorem(),
    );
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
    assert_theory_has_theorem(
        &theory,
        "nat_eq_zero_zero",
        nat_eq_zero_zero_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_eq_zero_succ",
        nat_eq_zero_succ_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_eq_succ_zero",
        nat_eq_succ_zero_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_eq_succ_succ",
        nat_eq_succ_succ_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_eq_zero_left",
        nat_eq_zero_left_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_eq_zero_right",
        nat_eq_zero_right_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "nat_eq_refl", nat_eq_refl_source_theorem());
    assert_theory_has_theorem(&theory, "nat_eq_is_bool", nat_eq_is_bool_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "nat_eq_pred_succ",
        nat_eq_pred_succ_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_le_zero_left",
        nat_le_zero_left_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_le_zero_right",
        nat_le_zero_right_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_le_succ_zero",
        nat_le_succ_zero_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_le_succ_succ",
        nat_le_succ_succ_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "nat_le_refl", nat_le_refl_source_theorem());
    assert_theory_has_theorem(&theory, "nat_le_is_bool", nat_le_is_bool_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "nat_lt_zero_zero",
        nat_lt_zero_zero_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_lt_zero_succ",
        nat_lt_zero_succ_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_lt_succ_zero",
        nat_lt_succ_zero_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_lt_succ_succ",
        nat_lt_succ_succ_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "nat_lt_irrefl", nat_lt_irrefl_source_theorem());
    assert_theory_has_theorem(&theory, "nat_lt_is_bool", nat_lt_is_bool_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "nat_le_list_suffix_cons",
        nat_le_list_suffix_cons_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_lt_list_suffix_cons",
        nat_lt_list_suffix_cons_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_le_self_succ",
        nat_le_self_succ_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_lt_self_succ",
        nat_lt_self_succ_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_lt_implies_nat_le",
        nat_lt_implies_nat_le_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_le_false_implies_nat_lt_right_left",
        nat_le_false_implies_nat_lt_right_left_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_lt_false_implies_nat_le_right_left",
        nat_lt_false_implies_nat_le_right_left_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "nat_le_trans", nat_le_trans_source_theorem());
    assert_theory_has_theorem(&theory, "nat_lt_trans", nat_lt_trans_source_theorem());
    assert_theory_has_theorem(&theory, "nat_le_lt_trans", nat_le_lt_trans_source_theorem());
    assert_theory_has_theorem(&theory, "nat_lt_le_trans", nat_lt_le_trans_source_theorem());
    assert_theory_has_theorem(&theory, "nat_eq_symm", nat_eq_symm_source_theorem());
    assert_theory_has_theorem(&theory, "nat_eq_trans", nat_eq_trans_source_theorem());
    assert_theory_has_theorem(&theory, "nat_eq_sound", nat_eq_sound_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "nat_eq_false_implies_nat_lt_or_nat_lt",
        nat_eq_false_implies_nat_lt_or_nat_lt_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_eq_implies_nat_le_left_right",
        nat_eq_implies_nat_le_left_right_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_eq_implies_nat_le_right_left",
        nat_eq_implies_nat_le_right_left_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "nat_le_antisymm", nat_le_antisymm_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "nat_le_implies_nat_lt_cons_right",
        nat_le_implies_nat_lt_cons_right_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "add_zero_left", add_zero_left_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "add_computes_to_list",
        add_computes_to_list_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "add_cons", add_cons_source_theorem());
    assert_theory_has_theorem(&theory, "nat_le_left_add", nat_le_left_add_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "nat_lt_left_add_succ_right",
        nat_lt_left_add_succ_right_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_le_right_add",
        nat_le_right_add_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_lt_nil_left_add",
        nat_lt_nil_left_add_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_le_add_right_mono",
        nat_le_add_right_mono_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_lt_add_right_mono",
        nat_lt_add_right_mono_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_le_add_left_mono",
        nat_le_add_left_mono_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_lt_add_left_mono",
        nat_lt_add_left_mono_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_le_add_left_cancel",
        nat_le_add_left_cancel_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_lt_add_left_cancel",
        nat_lt_add_left_cancel_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "add_succ_left", add_succ_left_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "pred_add_succ_left",
        pred_add_succ_left_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "is_zero_add_succ_left",
        is_zero_add_succ_left_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "add_cons_unit_right",
        add_cons_unit_right_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "add_succ_right", add_succ_right_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "pred_add_succ_right",
        pred_add_succ_right_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "is_zero_add_succ_right",
        is_zero_add_succ_right_source_theorem(),
    );
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
    assert_theory_has_theorem(
        &theory,
        "nat_le_add_right_cancel",
        nat_le_add_right_cancel_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_lt_add_right_cancel",
        nat_lt_add_right_cancel_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "add_swap", add_swap_source_theorem());
    assert_theory_has_theorem(&theory, "sub_zero_right", sub_zero_right_source_theorem());
    assert_theory_has_theorem(&theory, "sub_zero_left", sub_zero_left_source_theorem());
    assert_theory_has_theorem(&theory, "sub_succ_succ", sub_succ_succ_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "sub_computes_to_list",
        sub_computes_to_list_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "sub_preserves_nat_value",
        sub_preserves_nat_value_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "add_sub_cancel_left",
        add_sub_cancel_left_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "add_sub_cancel_right",
        add_sub_cancel_right_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "sub_self", sub_self_source_theorem());
    assert_theory_has_theorem(&theory, "nat_le_sub_left", nat_le_sub_left_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "nat_le_implies_sub_zero",
        nat_le_implies_sub_zero_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_le_of_sub_zero",
        nat_le_of_sub_zero_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_le_add_sub_cancel",
        nat_le_add_sub_cancel_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_le_add_sub_cancel_right",
        nat_le_add_sub_cancel_right_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_le_of_add_sub_cancel",
        nat_le_of_add_sub_cancel_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_lt_right_left_implies_nat_lt_zero_sub",
        nat_lt_right_left_implies_nat_lt_zero_sub_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_lt_zero_sub_implies_nat_lt_right_left",
        nat_lt_zero_sub_implies_nat_lt_right_left_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "mul_zero_left", mul_zero_left_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "is_zero_mul_zero_left",
        is_zero_mul_zero_left_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "mul_cons", mul_cons_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "mul_computes_to_list",
        mul_computes_to_list_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_le_mul_right_mono",
        nat_le_mul_right_mono_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_lt_mul_right_mono",
        nat_lt_mul_right_mono_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_le_mul_left_mono",
        nat_le_mul_left_mono_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "nat_lt_mul_left_mono",
        nat_lt_mul_left_mono_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "mul_preserves_nat_value",
        mul_preserves_nat_value_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "mul_succ_left", mul_succ_left_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "is_zero_mul_succ_succ",
        is_zero_mul_succ_succ_source_theorem(),
    );
    assert_theory_has_theorem(
        &theory,
        "pred_mul_succ_succ",
        pred_mul_succ_succ_source_theorem(),
    );
    assert_theory_has_theorem(&theory, "mul_succ_right", mul_succ_right_source_theorem());
    assert_theory_has_theorem(&theory, "mul_zero_right", mul_zero_right_source_theorem());
    assert_theory_has_theorem(
        &theory,
        "is_zero_mul_zero_right",
        is_zero_mul_zero_right_source_theorem(),
    );
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
