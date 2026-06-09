use super::*;

#[test]
fn nat_theorem_statements_load_from_source() {
    let zero_result = theorem_symbol("zero_computes_to_list", "result");
    let is_zero_bool_nat = theorem_symbol("is_zero_is_bool", "nat");
    let pred_succ_nat = theorem_symbol("pred_succ", "nat");
    let pred_result = theorem_symbol("pred_computes_to_list", "result");
    let pred_nat = theorem_symbol("pred_computes_to_list", "nat");
    let range_cons_head = theorem_symbol("range_cons", "head");
    let range_cons_tail = theorem_symbol("range_cons", "tail");
    let range_succ_nat = theorem_symbol("range_succ", "nat");
    let range_result = theorem_symbol("range_computes_to_list", "result");
    let range_count = theorem_symbol("range_computes_to_list", "count");
    let nat_eq_refl_nat = theorem_symbol("nat_eq_refl", "nat");
    let nat_eq_is_bool_left = theorem_symbol("nat_eq_is_bool", "left");
    let nat_eq_is_bool_right = theorem_symbol("nat_eq_is_bool", "right");
    let nat_le_refl_nat = theorem_symbol("nat_le_refl", "nat");
    let nat_le_is_bool_left = theorem_symbol("nat_le_is_bool", "left");
    let nat_le_is_bool_right = theorem_symbol("nat_le_is_bool", "right");
    let nat_lt_succ_succ_left = theorem_symbol("nat_lt_succ_succ", "left");
    let nat_lt_succ_succ_right = theorem_symbol("nat_lt_succ_succ", "right");
    let is_zero_cons_false_head = theorem_symbol("is_zero_cons_false", "head");
    let is_zero_cons_false_tail = theorem_symbol("is_zero_cons_false", "tail");
    let nat_lt_zero_cons_true_head = theorem_symbol("nat_lt_zero_cons_true", "head");
    let nat_lt_zero_cons_true_tail = theorem_symbol("nat_lt_zero_cons_true", "tail");
    let nat_le_cons_zero_false_head = theorem_symbol("nat_le_cons_zero_false", "head");
    let nat_le_cons_zero_false_tail = theorem_symbol("nat_le_cons_zero_false", "tail");
    let nat_lt_cons_zero_false_head = theorem_symbol("nat_lt_cons_zero_false", "head");
    let nat_lt_cons_zero_false_tail = theorem_symbol("nat_lt_cons_zero_false", "tail");
    let nat_lt_zero_implies_is_zero_false_nat =
        theorem_symbol("nat_lt_zero_implies_is_zero_false", "nat");
    let is_zero_false_implies_nat_lt_zero_nat =
        theorem_symbol("is_zero_false_implies_nat_lt_zero", "nat");
    let nat_lt_zero_implies_nat_le_zero_false_nat =
        theorem_symbol("nat_lt_zero_implies_nat_le_zero_false", "nat");
    let nat_lt_zero_implies_nat_lt_nat_zero_false_nat =
        theorem_symbol("nat_lt_zero_implies_nat_lt_nat_zero_false", "nat");
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
    let sub_add_right_left = theorem_symbol("sub_add_right", "left");
    let sub_add_right_right = theorem_symbol("sub_add_right", "right");
    let sub_add_right_middle = theorem_symbol("sub_add_right", "middle");
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
    let nat_le_of_add_sub_cancel_right_theorem_left =
        theorem_symbol("nat_le_of_add_sub_cancel_right", "left");
    let nat_le_of_add_sub_cancel_right_theorem_right =
        theorem_symbol("nat_le_of_add_sub_cancel_right", "right");
    let sub_add_cancel_left = theorem_symbol("sub_add_cancel", "left");
    let sub_add_cancel_right = theorem_symbol("sub_add_cancel", "right");
    let sub_add_cancel_middle = theorem_symbol("sub_add_cancel", "middle");
    let sub_add_left_left = theorem_symbol("sub_add_left", "left");
    let sub_add_left_right = theorem_symbol("sub_add_left", "right");
    let sub_add_left_middle = theorem_symbol("sub_add_left", "middle");
    let nat_le_sub_right_mono_left = theorem_symbol("nat_le_sub_right_mono", "left");
    let nat_le_sub_right_mono_right = theorem_symbol("nat_le_sub_right_mono", "right");
    let nat_le_sub_right_mono_middle = theorem_symbol("nat_le_sub_right_mono", "middle");
    let nat_le_sub_left_anti_left = theorem_symbol("nat_le_sub_left_anti", "left");
    let nat_le_sub_left_anti_right = theorem_symbol("nat_le_sub_left_anti", "right");
    let nat_le_sub_left_anti_middle = theorem_symbol("nat_le_sub_left_anti", "middle");
    let nat_lt_sub_right_mono_left = theorem_symbol("nat_lt_sub_right_mono", "left");
    let nat_lt_sub_right_mono_right = theorem_symbol("nat_lt_sub_right_mono", "right");
    let nat_lt_sub_right_mono_middle = theorem_symbol("nat_lt_sub_right_mono", "middle");
    let nat_eq_of_le_and_sub_zero_left = theorem_symbol("nat_eq_of_le_and_sub_zero", "left");
    let nat_eq_of_le_and_sub_zero_right = theorem_symbol("nat_eq_of_le_and_sub_zero", "right");
    let sub_eq_zero_of_nat_le_left = theorem_symbol("sub_eq_zero_of_nat_le", "left");
    let sub_eq_zero_of_nat_le_right = theorem_symbol("sub_eq_zero_of_nat_le", "right");
    let nat_le_of_sub_eq_zero_left = theorem_symbol("nat_le_of_sub_eq_zero", "left");
    let nat_le_of_sub_eq_zero_right = theorem_symbol("nat_le_of_sub_eq_zero", "right");
    let nat_le_implies_exists_add_left = theorem_symbol("nat_le_implies_exists_add", "left");
    let nat_le_implies_exists_add_right = theorem_symbol("nat_le_implies_exists_add", "right");
    let nat_le_implies_exists_add_difference =
        theorem_symbol("nat_le_implies_exists_add", "difference");
    let nat_le_of_exists_add_left = theorem_symbol("nat_le_of_exists_add", "left");
    let nat_le_of_exists_add_right = theorem_symbol("nat_le_of_exists_add", "right");
    let nat_le_of_exists_add_difference = theorem_symbol("nat_le_of_exists_add", "difference");
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
    let nat_lt_zero_mul_succ_left_left = theorem_symbol("nat_lt_zero_mul_succ_left", "left");
    let nat_lt_zero_mul_succ_left_right = theorem_symbol("nat_lt_zero_mul_succ_left", "right");
    let nat_lt_zero_mul_succ_succ_left = theorem_symbol("nat_lt_zero_mul_succ_succ", "left");
    let nat_lt_zero_mul_succ_succ_right = theorem_symbol("nat_lt_zero_mul_succ_succ", "right");
    let nat_lt_zero_mul_succ_right_left = theorem_symbol("nat_lt_zero_mul_succ_right", "left");
    let nat_lt_zero_mul_succ_right_right = theorem_symbol("nat_lt_zero_mul_succ_right", "right");
    let nat_lt_zero_mul_left = theorem_symbol("nat_lt_zero_mul", "left");
    let nat_lt_zero_mul_right = theorem_symbol("nat_lt_zero_mul", "right");
    let nat_lt_zero_mul_implies_left_left = theorem_symbol("nat_lt_zero_mul_implies_left", "left");
    let nat_lt_zero_mul_implies_left_right =
        theorem_symbol("nat_lt_zero_mul_implies_left", "right");
    let is_zero_mul_implies_is_zero_left =
        theorem_symbol("is_zero_mul_implies_is_zero_or_is_zero", "left");
    let is_zero_mul_implies_is_zero_right =
        theorem_symbol("is_zero_mul_implies_is_zero_or_is_zero", "right");
    let mul_zero_right_nat = theorem_symbol("mul_zero_right", "nat");
    let nat_lt_zero_mul_implies_right_left =
        theorem_symbol("nat_lt_zero_mul_implies_right", "left");
    let nat_lt_zero_mul_implies_right_right =
        theorem_symbol("nat_lt_zero_mul_implies_right", "right");
    let nat_le_mul_right_cancel_left = theorem_symbol("nat_le_mul_right_cancel", "left");
    let nat_le_mul_right_cancel_right = theorem_symbol("nat_le_mul_right_cancel", "right");
    let nat_le_mul_right_cancel_factor = theorem_symbol("nat_le_mul_right_cancel", "factor");
    let nat_lt_mul_right_cancel_left = theorem_symbol("nat_lt_mul_right_cancel", "left");
    let nat_lt_mul_right_cancel_right = theorem_symbol("nat_lt_mul_right_cancel", "right");
    let nat_lt_mul_right_cancel_factor = theorem_symbol("nat_lt_mul_right_cancel", "factor");
    let mul_one_left_right = theorem_symbol("mul_one_left", "right");
    let nat_le_mul_left_cancel_left = theorem_symbol("nat_le_mul_left_cancel", "left");
    let nat_le_mul_left_cancel_right = theorem_symbol("nat_le_mul_left_cancel", "right");
    let nat_le_mul_left_cancel_factor = theorem_symbol("nat_le_mul_left_cancel", "factor");
    let nat_lt_mul_left_cancel_left = theorem_symbol("nat_lt_mul_left_cancel", "left");
    let nat_lt_mul_left_cancel_right = theorem_symbol("nat_lt_mul_left_cancel", "right");
    let nat_lt_mul_left_cancel_factor = theorem_symbol("nat_lt_mul_left_cancel", "factor");

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
        range_zero_source_theorem(),
        computes_to(range_call(zero()), nil())
    );
    assert_eq!(
        range_cons_source_theorem(),
        crate::forall_where(
            range_cons_head,
            is_value(var(range_cons_head)),
            crate::forall_where(
                range_cons_tail,
                is_list(var(range_cons_tail)),
                computes_to(
                    range_call(cons(var(range_cons_head), var(range_cons_tail))),
                    snoc_call(range_call(var(range_cons_tail)), var(range_cons_tail))
                )
            )
        )
    );
    assert_eq!(
        range_succ_source_theorem(),
        forall_list(
            range_succ_nat,
            computes_to(
                range_call(succ_call(var(range_succ_nat))),
                snoc_call(range_call(var(range_succ_nat)), var(range_succ_nat))
            )
        )
    );
    assert_eq!(
        range_computes_to_list_source_theorem(),
        forall_list(
            range_count,
            computes_to_list(range_result, range_call(var(range_count)))
        )
    );
    assert_eq!(
        is_zero_cons_false_source_theorem(),
        crate::forall_where(
            is_zero_cons_false_head,
            is_value(var(is_zero_cons_false_head)),
            crate::forall_where(
                is_zero_cons_false_tail,
                is_list(var(is_zero_cons_false_tail)),
                computes_to(
                    is_zero_call(cons(
                        var(is_zero_cons_false_head),
                        var(is_zero_cons_false_tail)
                    )),
                    false_value()
                )
            )
        )
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
        nat_lt_zero_cons_true_source_theorem(),
        crate::forall_where(
            nat_lt_zero_cons_true_head,
            is_value(var(nat_lt_zero_cons_true_head)),
            crate::forall_where(
                nat_lt_zero_cons_true_tail,
                is_list(var(nat_lt_zero_cons_true_tail)),
                computes_to(
                    nat_lt_call(
                        zero(),
                        cons(
                            var(nat_lt_zero_cons_true_head),
                            var(nat_lt_zero_cons_true_tail)
                        )
                    ),
                    true_value()
                )
            )
        )
    );
    assert_eq!(
        nat_le_cons_zero_false_source_theorem(),
        crate::forall_where(
            nat_le_cons_zero_false_head,
            is_value(var(nat_le_cons_zero_false_head)),
            crate::forall_where(
                nat_le_cons_zero_false_tail,
                is_list(var(nat_le_cons_zero_false_tail)),
                computes_to(
                    nat_le_call(
                        cons(
                            var(nat_le_cons_zero_false_head),
                            var(nat_le_cons_zero_false_tail)
                        ),
                        zero()
                    ),
                    false_value()
                )
            )
        )
    );
    assert_eq!(
        nat_lt_cons_zero_false_source_theorem(),
        crate::forall_where(
            nat_lt_cons_zero_false_head,
            is_value(var(nat_lt_cons_zero_false_head)),
            crate::forall_where(
                nat_lt_cons_zero_false_tail,
                is_list(var(nat_lt_cons_zero_false_tail)),
                computes_to(
                    nat_lt_call(
                        cons(
                            var(nat_lt_cons_zero_false_head),
                            var(nat_lt_cons_zero_false_tail)
                        ),
                        zero()
                    ),
                    false_value()
                )
            )
        )
    );
    assert_eq!(
        nat_lt_zero_implies_is_zero_false_source_theorem(),
        forall_list(
            nat_lt_zero_implies_is_zero_false_nat,
            implies(
                computes_to(
                    nat_lt_call(zero(), var(nat_lt_zero_implies_is_zero_false_nat)),
                    true_value()
                ),
                computes_to(
                    is_zero_call(var(nat_lt_zero_implies_is_zero_false_nat)),
                    false_value()
                )
            )
        )
    );
    assert_eq!(
        is_zero_false_implies_nat_lt_zero_source_theorem(),
        forall_list(
            is_zero_false_implies_nat_lt_zero_nat,
            implies(
                computes_to(
                    is_zero_call(var(is_zero_false_implies_nat_lt_zero_nat)),
                    false_value()
                ),
                computes_to(
                    nat_lt_call(zero(), var(is_zero_false_implies_nat_lt_zero_nat)),
                    true_value()
                )
            )
        )
    );
    assert_eq!(
        nat_lt_zero_implies_nat_le_zero_false_source_theorem(),
        forall_list(
            nat_lt_zero_implies_nat_le_zero_false_nat,
            implies(
                computes_to(
                    nat_lt_call(zero(), var(nat_lt_zero_implies_nat_le_zero_false_nat)),
                    true_value()
                ),
                computes_to(
                    nat_le_call(var(nat_lt_zero_implies_nat_le_zero_false_nat), zero()),
                    false_value()
                )
            )
        )
    );
    assert_eq!(
        nat_lt_zero_implies_nat_lt_nat_zero_false_source_theorem(),
        forall_list(
            nat_lt_zero_implies_nat_lt_nat_zero_false_nat,
            implies(
                computes_to(
                    nat_lt_call(zero(), var(nat_lt_zero_implies_nat_lt_nat_zero_false_nat)),
                    true_value()
                ),
                computes_to(
                    nat_lt_call(var(nat_lt_zero_implies_nat_lt_nat_zero_false_nat), zero()),
                    false_value()
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
        sub_add_right_source_theorem(),
        forall_list(
            sub_add_right_left,
            forall_list(
                sub_add_right_right,
                forall_list(
                    sub_add_right_middle,
                    computes_to(
                        sub_call(
                            sub_call(var(sub_add_right_left), var(sub_add_right_right)),
                            var(sub_add_right_middle)
                        ),
                        sub_call(
                            var(sub_add_right_left),
                            add_call(var(sub_add_right_right), var(sub_add_right_middle))
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
        nat_le_of_add_sub_cancel_right_source_theorem(),
        forall_list(
            nat_le_of_add_sub_cancel_right_theorem_left,
            forall_list(
                nat_le_of_add_sub_cancel_right_theorem_right,
                implies(
                    nat_value_true(nat_le_of_add_sub_cancel_right_theorem_left),
                    implies(
                        nat_value_true(nat_le_of_add_sub_cancel_right_theorem_right),
                        implies(
                            computes_to(
                                add_call(
                                    sub_call(
                                        var(nat_le_of_add_sub_cancel_right_theorem_left),
                                        var(nat_le_of_add_sub_cancel_right_theorem_right)
                                    ),
                                    var(nat_le_of_add_sub_cancel_right_theorem_right)
                                ),
                                var(nat_le_of_add_sub_cancel_right_theorem_left)
                            ),
                            nat_le_true(
                                nat_le_of_add_sub_cancel_right_theorem_right,
                                nat_le_of_add_sub_cancel_right_theorem_left
                            )
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        sub_add_cancel_source_theorem(),
        forall_list(
            sub_add_cancel_left,
            forall_list(
                sub_add_cancel_right,
                forall_list(
                    sub_add_cancel_middle,
                    implies(
                        nat_value_true(sub_add_cancel_left),
                        implies(
                            nat_value_true(sub_add_cancel_right),
                            implies(
                                nat_le_true(sub_add_cancel_right, sub_add_cancel_left),
                                computes_to(
                                    sub_call(
                                        add_call(
                                            var(sub_add_cancel_left),
                                            var(sub_add_cancel_middle)
                                        ),
                                        var(sub_add_cancel_right)
                                    ),
                                    add_call(
                                        sub_call(
                                            var(sub_add_cancel_left),
                                            var(sub_add_cancel_right)
                                        ),
                                        var(sub_add_cancel_middle)
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
        sub_add_left_source_theorem(),
        forall_list(
            sub_add_left_left,
            forall_list(
                sub_add_left_right,
                forall_list(
                    sub_add_left_middle,
                    implies(
                        nat_value_true(sub_add_left_left),
                        implies(
                            nat_value_true(sub_add_left_right),
                            implies(
                                nat_value_true(sub_add_left_middle),
                                implies(
                                    nat_le_true(sub_add_left_right, sub_add_left_left),
                                    computes_to(
                                        sub_call(
                                            add_call(
                                                var(sub_add_left_middle),
                                                var(sub_add_left_left)
                                            ),
                                            var(sub_add_left_right)
                                        ),
                                        add_call(
                                            var(sub_add_left_middle),
                                            sub_call(
                                                var(sub_add_left_left),
                                                var(sub_add_left_right)
                                            )
                                        )
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
        nat_le_sub_right_mono_source_theorem(),
        forall_list(
            nat_le_sub_right_mono_left,
            forall_list(
                nat_le_sub_right_mono_right,
                forall_list(
                    nat_le_sub_right_mono_middle,
                    implies(
                        nat_le_true(nat_le_sub_right_mono_left, nat_le_sub_right_mono_right),
                        computes_to(
                            nat_le_call(
                                sub_call(
                                    var(nat_le_sub_right_mono_left),
                                    var(nat_le_sub_right_mono_middle)
                                ),
                                sub_call(
                                    var(nat_le_sub_right_mono_right),
                                    var(nat_le_sub_right_mono_middle)
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
        nat_le_sub_left_anti_source_theorem(),
        forall_list(
            nat_le_sub_left_anti_left,
            forall_list(
                nat_le_sub_left_anti_right,
                forall_list(
                    nat_le_sub_left_anti_middle,
                    implies(
                        nat_le_true(nat_le_sub_left_anti_left, nat_le_sub_left_anti_right),
                        computes_to(
                            nat_le_call(
                                sub_call(
                                    var(nat_le_sub_left_anti_middle),
                                    var(nat_le_sub_left_anti_right)
                                ),
                                sub_call(
                                    var(nat_le_sub_left_anti_middle),
                                    var(nat_le_sub_left_anti_left)
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
        nat_lt_sub_right_mono_source_theorem(),
        forall_list(
            nat_lt_sub_right_mono_left,
            forall_list(
                nat_lt_sub_right_mono_right,
                forall_list(
                    nat_lt_sub_right_mono_middle,
                    implies(
                        nat_lt_true(nat_lt_sub_right_mono_left, nat_lt_sub_right_mono_right),
                        implies(
                            nat_le_true(nat_lt_sub_right_mono_middle, nat_lt_sub_right_mono_left),
                            computes_to(
                                nat_lt_call(
                                    sub_call(
                                        var(nat_lt_sub_right_mono_left),
                                        var(nat_lt_sub_right_mono_middle)
                                    ),
                                    sub_call(
                                        var(nat_lt_sub_right_mono_right),
                                        var(nat_lt_sub_right_mono_middle)
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
        nat_eq_of_le_and_sub_zero_source_theorem(),
        forall_list(
            nat_eq_of_le_and_sub_zero_left,
            forall_list(
                nat_eq_of_le_and_sub_zero_right,
                implies(
                    nat_value_true(nat_eq_of_le_and_sub_zero_left),
                    implies(
                        nat_value_true(nat_eq_of_le_and_sub_zero_right),
                        implies(
                            nat_le_true(
                                nat_eq_of_le_and_sub_zero_left,
                                nat_eq_of_le_and_sub_zero_right
                            ),
                            implies(
                                computes_to(
                                    sub_call(
                                        var(nat_eq_of_le_and_sub_zero_right),
                                        var(nat_eq_of_le_and_sub_zero_left)
                                    ),
                                    zero()
                                ),
                                computes_to(
                                    var(nat_eq_of_le_and_sub_zero_left),
                                    var(nat_eq_of_le_and_sub_zero_right)
                                )
                            )
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        sub_eq_zero_of_nat_le_source_theorem(),
        forall_list(
            sub_eq_zero_of_nat_le_left,
            forall_list(
                sub_eq_zero_of_nat_le_right,
                implies(
                    nat_le_true(sub_eq_zero_of_nat_le_left, sub_eq_zero_of_nat_le_right),
                    computes_to(
                        sub_call(
                            var(sub_eq_zero_of_nat_le_left),
                            var(sub_eq_zero_of_nat_le_right)
                        ),
                        zero()
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_le_of_sub_eq_zero_source_theorem(),
        forall_list(
            nat_le_of_sub_eq_zero_left,
            forall_list(
                nat_le_of_sub_eq_zero_right,
                implies(
                    computes_to(
                        sub_call(
                            var(nat_le_of_sub_eq_zero_left),
                            var(nat_le_of_sub_eq_zero_right)
                        ),
                        zero()
                    ),
                    nat_le_true(nat_le_of_sub_eq_zero_left, nat_le_of_sub_eq_zero_right)
                )
            )
        )
    );
    assert_eq!(
        nat_le_implies_exists_add_source_theorem(),
        forall_list(
            nat_le_implies_exists_add_left,
            forall_list(
                nat_le_implies_exists_add_right,
                implies(
                    nat_value_true(nat_le_implies_exists_add_left),
                    implies(
                        nat_value_true(nat_le_implies_exists_add_right),
                        implies(
                            nat_le_true(
                                nat_le_implies_exists_add_left,
                                nat_le_implies_exists_add_right
                            ),
                            crate::exists_where(
                                nat_le_implies_exists_add_difference,
                                is_list(var(nat_le_implies_exists_add_difference)),
                                computes_to(
                                    add_call(
                                        var(nat_le_implies_exists_add_left),
                                        var(nat_le_implies_exists_add_difference)
                                    ),
                                    var(nat_le_implies_exists_add_right)
                                )
                            )
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_le_of_exists_add_source_theorem(),
        forall_list(
            nat_le_of_exists_add_left,
            forall_list(
                nat_le_of_exists_add_right,
                implies(
                    crate::exists_where(
                        nat_le_of_exists_add_difference,
                        is_list(var(nat_le_of_exists_add_difference)),
                        computes_to(
                            add_call(
                                var(nat_le_of_exists_add_left),
                                var(nat_le_of_exists_add_difference)
                            ),
                            var(nat_le_of_exists_add_right)
                        )
                    ),
                    nat_le_true(nat_le_of_exists_add_left, nat_le_of_exists_add_right)
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
        nat_lt_zero_mul_succ_left_source_theorem(),
        forall_list(
            nat_lt_zero_mul_succ_left_left,
            forall_list(
                nat_lt_zero_mul_succ_left_right,
                implies(
                    computes_to(
                        nat_lt_call(zero(), var(nat_lt_zero_mul_succ_left_right)),
                        true_value()
                    ),
                    computes_to(
                        nat_lt_call(
                            zero(),
                            mul_call(
                                succ_call(var(nat_lt_zero_mul_succ_left_left)),
                                var(nat_lt_zero_mul_succ_left_right)
                            )
                        ),
                        true_value()
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_lt_zero_mul_succ_succ_source_theorem(),
        forall_list(
            nat_lt_zero_mul_succ_succ_left,
            forall_list(
                nat_lt_zero_mul_succ_succ_right,
                computes_to(
                    nat_lt_call(
                        zero(),
                        mul_call(
                            succ_call(var(nat_lt_zero_mul_succ_succ_left)),
                            succ_call(var(nat_lt_zero_mul_succ_succ_right))
                        )
                    ),
                    true_value()
                )
            )
        )
    );
    assert_eq!(
        nat_lt_zero_mul_succ_right_source_theorem(),
        forall_list(
            nat_lt_zero_mul_succ_right_left,
            forall_list(
                nat_lt_zero_mul_succ_right_right,
                implies(
                    nat_value_true(nat_lt_zero_mul_succ_right_left),
                    implies(
                        nat_value_true(nat_lt_zero_mul_succ_right_right),
                        implies(
                            computes_to(
                                nat_lt_call(zero(), var(nat_lt_zero_mul_succ_right_left)),
                                true_value()
                            ),
                            computes_to(
                                nat_lt_call(
                                    zero(),
                                    mul_call(
                                        var(nat_lt_zero_mul_succ_right_left),
                                        succ_call(var(nat_lt_zero_mul_succ_right_right))
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
        nat_lt_zero_mul_source_theorem(),
        forall_list(
            nat_lt_zero_mul_left,
            forall_list(
                nat_lt_zero_mul_right,
                implies(
                    computes_to(nat_lt_call(zero(), var(nat_lt_zero_mul_left)), true_value()),
                    implies(
                        computes_to(
                            nat_lt_call(zero(), var(nat_lt_zero_mul_right)),
                            true_value()
                        ),
                        computes_to(
                            nat_lt_call(
                                zero(),
                                mul_call(var(nat_lt_zero_mul_left), var(nat_lt_zero_mul_right))
                            ),
                            true_value()
                        )
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_lt_zero_mul_implies_left_source_theorem(),
        forall_list(
            nat_lt_zero_mul_implies_left_left,
            forall_list(
                nat_lt_zero_mul_implies_left_right,
                implies(
                    computes_to(
                        nat_lt_call(
                            zero(),
                            mul_call(
                                var(nat_lt_zero_mul_implies_left_left),
                                var(nat_lt_zero_mul_implies_left_right)
                            )
                        ),
                        true_value()
                    ),
                    computes_to(
                        nat_lt_call(zero(), var(nat_lt_zero_mul_implies_left_left)),
                        true_value()
                    )
                )
            )
        )
    );
    assert_eq!(
        is_zero_mul_implies_is_zero_or_is_zero_source_theorem(),
        forall_list(
            is_zero_mul_implies_is_zero_left,
            forall_list(
                is_zero_mul_implies_is_zero_right,
                implies(
                    computes_to(
                        is_zero_call(mul_call(
                            var(is_zero_mul_implies_is_zero_left),
                            var(is_zero_mul_implies_is_zero_right)
                        )),
                        true_value()
                    ),
                    or(
                        computes_to(
                            is_zero_call(var(is_zero_mul_implies_is_zero_left)),
                            true_value()
                        ),
                        computes_to(
                            is_zero_call(var(is_zero_mul_implies_is_zero_right)),
                            true_value()
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
        nat_lt_zero_mul_implies_right_source_theorem(),
        forall_list(
            nat_lt_zero_mul_implies_right_left,
            forall_list(
                nat_lt_zero_mul_implies_right_right,
                implies(
                    computes_to(
                        nat_lt_call(
                            zero(),
                            mul_call(
                                var(nat_lt_zero_mul_implies_right_left),
                                var(nat_lt_zero_mul_implies_right_right)
                            )
                        ),
                        true_value()
                    ),
                    computes_to(
                        nat_lt_call(zero(), var(nat_lt_zero_mul_implies_right_right)),
                        true_value()
                    )
                )
            )
        )
    );
    assert_eq!(
        nat_le_mul_right_cancel_source_theorem(),
        forall_list(
            nat_le_mul_right_cancel_left,
            forall_list(
                nat_le_mul_right_cancel_right,
                forall_list(
                    nat_le_mul_right_cancel_factor,
                    implies(
                        computes_to(
                            nat_lt_call(zero(), var(nat_le_mul_right_cancel_factor)),
                            true_value()
                        ),
                        implies(
                            computes_to(
                                nat_le_call(
                                    mul_call(
                                        var(nat_le_mul_right_cancel_left),
                                        var(nat_le_mul_right_cancel_factor)
                                    ),
                                    mul_call(
                                        var(nat_le_mul_right_cancel_right),
                                        var(nat_le_mul_right_cancel_factor)
                                    )
                                ),
                                true_value()
                            ),
                            computes_to(
                                nat_le_call(
                                    var(nat_le_mul_right_cancel_left),
                                    var(nat_le_mul_right_cancel_right)
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
        nat_lt_mul_right_cancel_source_theorem(),
        forall_list(
            nat_lt_mul_right_cancel_left,
            forall_list(
                nat_lt_mul_right_cancel_right,
                forall_list(
                    nat_lt_mul_right_cancel_factor,
                    implies(
                        computes_to(
                            nat_lt_call(zero(), var(nat_lt_mul_right_cancel_factor)),
                            true_value()
                        ),
                        implies(
                            computes_to(
                                nat_lt_call(
                                    mul_call(
                                        var(nat_lt_mul_right_cancel_left),
                                        var(nat_lt_mul_right_cancel_factor)
                                    ),
                                    mul_call(
                                        var(nat_lt_mul_right_cancel_right),
                                        var(nat_lt_mul_right_cancel_factor)
                                    )
                                ),
                                true_value()
                            ),
                            computes_to(
                                nat_lt_call(
                                    var(nat_lt_mul_right_cancel_left),
                                    var(nat_lt_mul_right_cancel_right)
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
    assert_eq!(
        nat_le_mul_left_cancel_source_theorem(),
        forall_list(
            nat_le_mul_left_cancel_left,
            forall_list(
                nat_le_mul_left_cancel_right,
                forall_list(
                    nat_le_mul_left_cancel_factor,
                    implies(
                        nat_value_true(nat_le_mul_left_cancel_left),
                        implies(
                            nat_value_true(nat_le_mul_left_cancel_right),
                            implies(
                                nat_value_true(nat_le_mul_left_cancel_factor),
                                implies(
                                    computes_to(
                                        nat_lt_call(zero(), var(nat_le_mul_left_cancel_factor)),
                                        true_value()
                                    ),
                                    implies(
                                        computes_to(
                                            nat_le_call(
                                                mul_call(
                                                    var(nat_le_mul_left_cancel_factor),
                                                    var(nat_le_mul_left_cancel_left)
                                                ),
                                                mul_call(
                                                    var(nat_le_mul_left_cancel_factor),
                                                    var(nat_le_mul_left_cancel_right)
                                                )
                                            ),
                                            true_value()
                                        ),
                                        computes_to(
                                            nat_le_call(
                                                var(nat_le_mul_left_cancel_left),
                                                var(nat_le_mul_left_cancel_right)
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
        )
    );
    assert_eq!(
        nat_lt_mul_left_cancel_source_theorem(),
        forall_list(
            nat_lt_mul_left_cancel_left,
            forall_list(
                nat_lt_mul_left_cancel_right,
                forall_list(
                    nat_lt_mul_left_cancel_factor,
                    implies(
                        nat_value_true(nat_lt_mul_left_cancel_left),
                        implies(
                            nat_value_true(nat_lt_mul_left_cancel_right),
                            implies(
                                nat_value_true(nat_lt_mul_left_cancel_factor),
                                implies(
                                    computes_to(
                                        nat_lt_call(zero(), var(nat_lt_mul_left_cancel_factor)),
                                        true_value()
                                    ),
                                    implies(
                                        computes_to(
                                            nat_lt_call(
                                                mul_call(
                                                    var(nat_lt_mul_left_cancel_factor),
                                                    var(nat_lt_mul_left_cancel_left)
                                                ),
                                                mul_call(
                                                    var(nat_lt_mul_left_cancel_factor),
                                                    var(nat_lt_mul_left_cancel_right)
                                                )
                                            ),
                                            true_value()
                                        ),
                                        computes_to(
                                            nat_lt_call(
                                                var(nat_lt_mul_left_cancel_left),
                                                var(nat_lt_mul_left_cancel_right)
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
        )
    );
}
