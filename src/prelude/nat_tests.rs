//! Test helpers and expected behavior for the nat prelude source.

use crate::{
    Computation, Lambda, Prop, Symbol, Theory, computes_to, computes_to_list, forall_where,
    implies, is_bool, is_list, is_value, or,
};

use super::list_tests::{
    apply, check_evaluates_to, cons, false_value, length_call, nil, proof_by_evaluation, quote,
    snoc_call, true_value, unit, var,
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

pub fn range() -> Computation {
    computation_ref("range")
}

pub fn range_definition() -> Computation {
    definition("range")
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

pub fn range_call(count: Computation) -> Computation {
    apply(range(), count)
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

pub fn succ_injective_source_theorem() -> Prop {
    theorem_prop("succ_injective")
}

pub fn zero_ne_succ_source_theorem() -> Prop {
    theorem_prop("zero_ne_succ")
}

pub fn is_zero_zero_source_theorem() -> Prop {
    theorem_prop("is_zero_zero")
}

pub fn is_zero_succ_source_theorem() -> Prop {
    theorem_prop("is_zero_succ")
}

pub fn is_zero_cons_false_source_theorem() -> Prop {
    theorem_prop("is_zero_cons_false")
}

pub fn is_zero_is_bool_source_theorem() -> Prop {
    theorem_prop("is_zero_is_bool")
}

pub fn is_zero_computes_to_bool_source_theorem() -> Prop {
    theorem_prop("is_zero_computes_to_bool")
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

pub fn pred_preserves_nat_value_source_theorem() -> Prop {
    theorem_prop("pred_preserves_nat_value")
}

pub fn pred_succ_inverse_source_theorem() -> Prop {
    theorem_prop("pred_succ_inverse")
}

pub fn succ_computes_to_list_source_theorem() -> Prop {
    theorem_prop("succ_computes_to_list")
}

pub fn succ_pred_inverse_for_nonzero_source_theorem() -> Prop {
    theorem_prop("succ_pred_inverse_for_nonzero")
}

pub fn range_zero_source_theorem() -> Prop {
    theorem_prop("range_zero")
}

pub fn range_cons_source_theorem() -> Prop {
    theorem_prop("range_cons")
}

pub fn range_succ_source_theorem() -> Prop {
    theorem_prop("range_succ")
}

pub fn range_computes_to_list_source_theorem() -> Prop {
    theorem_prop("range_computes_to_list")
}

pub fn length_range_source_theorem() -> Prop {
    theorem_prop("length_range")
}

pub fn succ_preserves_nat_value_source_theorem() -> Prop {
    theorem_prop("succ_preserves_nat_value")
}

pub fn is_nat_value_nil_source_theorem() -> Prop {
    theorem_prop("is_nat_value_nil")
}

pub fn is_nat_value_cons_source_theorem() -> Prop {
    theorem_prop("is_nat_value_cons")
}

pub fn is_nat_value_cons_true_elim_source_theorem() -> Prop {
    theorem_prop("is_nat_value_cons_true_elim")
}

pub fn is_nat_value_tail_source_theorem() -> Prop {
    theorem_prop("is_nat_value_tail")
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

pub fn nat_eq_computes_to_bool_source_theorem() -> Prop {
    theorem_prop("nat_eq_computes_to_bool")
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

pub fn nat_le_of_equal_lists_source_theorem() -> Prop {
    theorem_prop("nat_le_of_equal_lists")
}

pub fn nat_le_is_bool_source_theorem() -> Prop {
    theorem_prop("nat_le_is_bool")
}

pub fn nat_le_computes_to_bool_source_theorem() -> Prop {
    theorem_prop("nat_le_computes_to_bool")
}

pub fn nat_lt_zero_zero_source_theorem() -> Prop {
    theorem_prop("nat_lt_zero_zero")
}

pub fn nat_lt_zero_succ_source_theorem() -> Prop {
    theorem_prop("nat_lt_zero_succ")
}

pub fn nat_lt_zero_cons_true_source_theorem() -> Prop {
    theorem_prop("nat_lt_zero_cons_true")
}

pub fn nat_le_cons_zero_false_source_theorem() -> Prop {
    theorem_prop("nat_le_cons_zero_false")
}

pub fn nat_lt_cons_zero_false_source_theorem() -> Prop {
    theorem_prop("nat_lt_cons_zero_false")
}

pub fn nat_lt_zero_implies_is_zero_false_source_theorem() -> Prop {
    theorem_prop("nat_lt_zero_implies_is_zero_false")
}

pub fn is_zero_false_implies_nat_lt_zero_source_theorem() -> Prop {
    theorem_prop("is_zero_false_implies_nat_lt_zero")
}

pub fn nat_lt_zero_implies_nat_le_zero_false_source_theorem() -> Prop {
    theorem_prop("nat_lt_zero_implies_nat_le_zero_false")
}

pub fn nat_lt_zero_implies_nat_lt_nat_zero_false_source_theorem() -> Prop {
    theorem_prop("nat_lt_zero_implies_nat_lt_nat_zero_false")
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

pub fn nat_lt_computes_to_bool_source_theorem() -> Prop {
    theorem_prop("nat_lt_computes_to_bool")
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

pub fn nat_le_succ_right_source_theorem() -> Prop {
    theorem_prop("nat_le_succ_right")
}

pub fn nat_lt_self_succ_source_theorem() -> Prop {
    theorem_prop("nat_lt_self_succ")
}

pub fn nat_lt_succ_self_source_theorem() -> Prop {
    theorem_prop("nat_lt_succ_self")
}

pub fn nat_lt_implies_nat_le_source_theorem() -> Prop {
    theorem_prop("nat_lt_implies_nat_le")
}

pub fn nat_lt_implies_le_source_theorem() -> Prop {
    theorem_prop("nat_lt_implies_le")
}

pub fn nat_le_false_implies_nat_lt_right_left_source_theorem() -> Prop {
    theorem_prop("nat_le_false_implies_nat_lt_right_left")
}

pub fn nat_lt_false_implies_nat_le_right_left_source_theorem() -> Prop {
    theorem_prop("nat_lt_false_implies_nat_le_right_left")
}

pub fn nat_le_total_source_theorem() -> Prop {
    theorem_prop("nat_le_total")
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

pub fn nat_eq_true_implies_equal_source_theorem() -> Prop {
    theorem_prop("nat_eq_true_implies_equal")
}

pub fn nat_eq_false_implies_not_equal_source_theorem() -> Prop {
    theorem_prop("nat_eq_false_implies_not_equal")
}

pub fn nat_lt_implies_nat_eq_false_source_theorem() -> Prop {
    theorem_prop("nat_lt_implies_nat_eq_false")
}

pub fn nat_lt_as_le_and_not_eq_source_theorem() -> Prop {
    theorem_prop("nat_lt_as_le_and_not_eq")
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

pub fn nat_le_and_ne_implies_lt_source_theorem() -> Prop {
    theorem_prop("nat_le_and_ne_implies_lt")
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

pub fn nat_le_add_right_source_theorem() -> Prop {
    theorem_prop("nat_le_add_right")
}

pub fn nat_le_add_left_source_theorem() -> Prop {
    theorem_prop("nat_le_add_left")
}

pub fn nat_lt_nil_left_add_source_theorem() -> Prop {
    theorem_prop("nat_lt_nil_left_add")
}

pub fn nat_lt_add_right_source_theorem() -> Prop {
    theorem_prop("nat_lt_add_right")
}

pub fn nat_lt_add_left_source_theorem() -> Prop {
    theorem_prop("nat_lt_add_left")
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

pub fn nat_le_add_cancel_left_source_theorem() -> Prop {
    theorem_prop("nat_le_add_cancel_left")
}

pub fn nat_lt_add_cancel_left_source_theorem() -> Prop {
    theorem_prop("nat_lt_add_cancel_left")
}

pub fn nat_le_add_right_cancel_source_theorem() -> Prop {
    theorem_prop("nat_le_add_right_cancel")
}

pub fn nat_lt_add_right_cancel_source_theorem() -> Prop {
    theorem_prop("nat_lt_add_right_cancel")
}

pub fn nat_le_add_cancel_right_source_theorem() -> Prop {
    theorem_prop("nat_le_add_cancel_right")
}

pub fn nat_lt_add_cancel_right_source_theorem() -> Prop {
    theorem_prop("nat_lt_add_cancel_right")
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

pub fn add_left_cancel_source_theorem() -> Prop {
    theorem_prop("add_left_cancel")
}

pub fn add_right_cancel_source_theorem() -> Prop {
    theorem_prop("add_right_cancel")
}

pub fn add_left_eq_zero_source_theorem() -> Prop {
    theorem_prop("add_left_eq_zero")
}

pub fn add_right_eq_zero_source_theorem() -> Prop {
    theorem_prop("add_right_eq_zero")
}

pub fn add_eq_zero_cases_source_theorem() -> Prop {
    theorem_prop("add_eq_zero_cases")
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

pub fn sub_add_right_source_theorem() -> Prop {
    theorem_prop("sub_add_right")
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

pub fn nat_le_of_add_sub_cancel_right_source_theorem() -> Prop {
    theorem_prop("nat_le_of_add_sub_cancel_right")
}

pub fn sub_add_cancel_source_theorem() -> Prop {
    theorem_prop("sub_add_cancel")
}

pub fn sub_add_left_source_theorem() -> Prop {
    theorem_prop("sub_add_left")
}

pub fn nat_le_sub_right_mono_source_theorem() -> Prop {
    theorem_prop("nat_le_sub_right_mono")
}

pub fn nat_le_sub_left_anti_source_theorem() -> Prop {
    theorem_prop("nat_le_sub_left_anti")
}

pub fn sub_monotone_left_source_theorem() -> Prop {
    theorem_prop("sub_monotone_left")
}

pub fn sub_monotone_right_source_theorem() -> Prop {
    theorem_prop("sub_monotone_right")
}

pub fn nat_lt_sub_right_mono_source_theorem() -> Prop {
    theorem_prop("nat_lt_sub_right_mono")
}

pub fn nat_eq_of_le_and_sub_zero_source_theorem() -> Prop {
    theorem_prop("nat_eq_of_le_and_sub_zero")
}

pub fn sub_eq_zero_of_nat_le_source_theorem() -> Prop {
    theorem_prop("sub_eq_zero_of_nat_le")
}

pub fn sub_eq_zero_of_le_source_theorem() -> Prop {
    theorem_prop("sub_eq_zero_of_le")
}

pub fn nat_le_of_sub_eq_zero_source_theorem() -> Prop {
    theorem_prop("nat_le_of_sub_eq_zero")
}

pub fn nat_le_implies_exists_add_source_theorem() -> Prop {
    theorem_prop("nat_le_implies_exists_add")
}

pub fn nat_le_of_exists_add_source_theorem() -> Prop {
    theorem_prop("nat_le_of_exists_add")
}

pub fn nat_lt_right_left_implies_nat_lt_zero_sub_source_theorem() -> Prop {
    theorem_prop("nat_lt_right_left_implies_nat_lt_zero_sub")
}

pub fn sub_pos_of_lt_source_theorem() -> Prop {
    theorem_prop("sub_pos_of_lt")
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

pub fn nat_le_mul_positive_right_source_theorem() -> Prop {
    theorem_prop("nat_le_mul_positive_right")
}

pub fn nat_lt_mul_positive_right_source_theorem() -> Prop {
    theorem_prop("nat_lt_mul_positive_right")
}

pub fn nat_le_mul_left_mono_source_theorem() -> Prop {
    theorem_prop("nat_le_mul_left_mono")
}

pub fn nat_lt_mul_left_mono_source_theorem() -> Prop {
    theorem_prop("nat_lt_mul_left_mono")
}

pub fn nat_le_mul_positive_left_source_theorem() -> Prop {
    theorem_prop("nat_le_mul_positive_left")
}

pub fn nat_lt_mul_positive_left_source_theorem() -> Prop {
    theorem_prop("nat_lt_mul_positive_left")
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

pub fn nat_lt_zero_mul_succ_left_source_theorem() -> Prop {
    theorem_prop("nat_lt_zero_mul_succ_left")
}

pub fn nat_lt_zero_mul_succ_succ_source_theorem() -> Prop {
    theorem_prop("nat_lt_zero_mul_succ_succ")
}

pub fn pred_mul_succ_succ_source_theorem() -> Prop {
    theorem_prop("pred_mul_succ_succ")
}

pub fn mul_succ_right_source_theorem() -> Prop {
    theorem_prop("mul_succ_right")
}

pub fn nat_lt_zero_mul_succ_right_source_theorem() -> Prop {
    theorem_prop("nat_lt_zero_mul_succ_right")
}

pub fn nat_lt_zero_mul_source_theorem() -> Prop {
    theorem_prop("nat_lt_zero_mul")
}

pub fn nat_lt_zero_mul_implies_left_source_theorem() -> Prop {
    theorem_prop("nat_lt_zero_mul_implies_left")
}

pub fn is_zero_mul_implies_is_zero_or_is_zero_source_theorem() -> Prop {
    theorem_prop("is_zero_mul_implies_is_zero_or_is_zero")
}

pub fn mul_eq_zero_cases_source_theorem() -> Prop {
    theorem_prop("mul_eq_zero_cases")
}

pub fn mul_zero_right_source_theorem() -> Prop {
    theorem_prop("mul_zero_right")
}

pub fn nat_lt_zero_mul_implies_right_source_theorem() -> Prop {
    theorem_prop("nat_lt_zero_mul_implies_right")
}

pub fn nat_le_mul_right_cancel_source_theorem() -> Prop {
    theorem_prop("nat_le_mul_right_cancel")
}

pub fn nat_lt_mul_right_cancel_source_theorem() -> Prop {
    theorem_prop("nat_lt_mul_right_cancel")
}

pub fn mul_right_cancel_positive_source_theorem() -> Prop {
    theorem_prop("mul_right_cancel_positive")
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

pub fn mul_left_cancel_positive_source_theorem() -> Prop {
    theorem_prop("mul_left_cancel_positive")
}

pub fn nat_le_mul_left_cancel_source_theorem() -> Prop {
    theorem_prop("nat_le_mul_left_cancel")
}

pub fn nat_lt_mul_left_cancel_source_theorem() -> Prop {
    theorem_prop("nat_lt_mul_left_cancel")
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
    let modules = super::parsed_nat_modules().expect("prelude nat source should parse");
    let env = super::parsed_prelude_env().expect("prelude source should parse");
    let name = env
        .computation(spelling)
        .expect("prelude nat source should define requested computation name");

    modules
        .iter()
        .find_map(|module| module.computation(name))
        .cloned()
        .expect("prelude nat source should define requested computation")
}

fn theorem_prop(spelling: &str) -> Prop {
    theorem_definition(spelling).prop
}

fn theorem_definition(spelling: &str) -> crate::elab::source::ParsedTheorem {
    let modules = super::parsed_nat_modules().expect("prelude nat source should parse");
    let env = super::parsed_prelude_env().expect("prelude source should parse");
    let name = env
        .theorem(spelling)
        .expect("prelude nat source should define requested theorem name");

    modules
        .iter()
        .find_map(|module| module.theorem(name))
        .cloned()
        .expect("prelude nat source should define requested theorem")
}

fn theorem_symbol(theorem: &str, spelling: &str) -> Symbol {
    theorem_definition(theorem)
        .symbol(spelling)
        .expect("prelude nat source should define requested theorem symbol once")
}

fn forall_list(symbol: Symbol, body: Prop) -> Prop {
    crate::forall_where(symbol, is_list(var(symbol)), body)
}

fn nat_value_true(symbol: Symbol) -> Prop {
    computes_to(is_nat_value_call(var(symbol)), true_value())
}

pub fn length_range_theorem(count: Symbol) -> Prop {
    forall_where(
        count,
        is_list(var(count)),
        implies(
            nat_value_true(count),
            computes_to(length_call(range_call(var(count))), var(count)),
        ),
    )
}

fn nat_le_true(left: Symbol, right: Symbol) -> Prop {
    computes_to(nat_le_call(var(left), var(right)), true_value())
}

fn nat_lt_true(left: Symbol, right: Symbol) -> Prop {
    computes_to(nat_lt_call(var(left), var(right)), true_value())
}

mod definitions;
mod evaluation;
mod statements;
mod theory;
