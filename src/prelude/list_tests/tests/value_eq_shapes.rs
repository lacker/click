use super::*;

#[test]
fn value_eq_source_theorems_have_expected_shape() {
    let nil_cons_head = theorem_symbol("value_eq_nil_cons", "head");
    let nil_cons_tail = theorem_symbol("value_eq_nil_cons", "tail");
    let cons_nil_head = theorem_symbol("value_eq_cons_nil", "head");
    let cons_nil_tail = theorem_symbol("value_eq_cons_nil", "tail");
    let cons_left_head = theorem_symbol("value_eq_cons", "left_head");
    let cons_left_tail = theorem_symbol("value_eq_cons", "left_tail");
    let cons_right_head = theorem_symbol("value_eq_cons", "right_head");
    let cons_right_tail = theorem_symbol("value_eq_cons", "right_tail");
    let kind_symbol_value = theorem_symbol("value_kind_symbol_implies_is_symbol", "value");
    let kind_lambda_value = theorem_symbol("value_kind_lambda_implies_is_lambda", "value");
    let symbol_not_lambda_value = theorem_symbol("is_symbol_true_implies_is_lambda_false", "value");
    let comparable_symbol_value = theorem_symbol("value_eq_comparable_symbol", "value");
    let comparable_cons_head = theorem_symbol("value_eq_comparable_cons", "head");
    let comparable_cons_tail = theorem_symbol("value_eq_comparable_cons", "tail");
    let not_lambdas_left = theorem_symbol("value_eq_true_implies_not_lambdas", "left");
    let not_lambdas_right = theorem_symbol("value_eq_true_implies_not_lambdas", "right");
    let classified_list_value = theorem_symbol("value_non_symbol_non_lambda_is_list", "value");
    let non_symbol_lists_left =
        theorem_symbol("value_eq_left_non_symbol_true_implies_lists", "left");
    let non_symbol_lists_right =
        theorem_symbol("value_eq_left_non_symbol_true_implies_lists", "right");
    let left_symbol_left = theorem_symbol("value_eq_left_symbol_true", "left");
    let left_symbol_right = theorem_symbol("value_eq_left_symbol_true", "right");
    let left_symbol_sound_left = theorem_symbol("value_eq_left_symbol_sound", "left");
    let left_symbol_sound_right = theorem_symbol("value_eq_left_symbol_sound", "right");
    let cons_elim_left_head = theorem_symbol("value_eq_cons_true_elim", "left_head");
    let cons_elim_left_tail = theorem_symbol("value_eq_cons_true_elim", "left_tail");
    let cons_elim_right_head = theorem_symbol("value_eq_cons_true_elim", "right_head");
    let cons_elim_right_tail = theorem_symbol("value_eq_cons_true_elim", "right_tail");
    let cons_congr_left_head = theorem_symbol("cons_congr", "left_head");
    let cons_congr_left_tail = theorem_symbol("cons_congr", "left_tail");
    let cons_congr_right_head = theorem_symbol("cons_congr", "right_head");
    let cons_congr_right_tail = theorem_symbol("cons_congr", "right_tail");
    let sound_left = theorem_symbol("value_eq_sound", "left");
    let sound_right = theorem_symbol("value_eq_sound", "right");
    let refl_value = theorem_symbol("value_eq_refl", "value");
    let comparable_left_left = theorem_symbol("value_eq_true_implies_comparable_left", "left");
    let comparable_left_right = theorem_symbol("value_eq_true_implies_comparable_left", "right");
    let comparable_right_left = theorem_symbol("value_eq_true_implies_comparable_right", "left");
    let comparable_right_right = theorem_symbol("value_eq_true_implies_comparable_right", "right");
    let symm_left = theorem_symbol("value_eq_symm", "left");
    let symm_right = theorem_symbol("value_eq_symm", "right");

    assert_eq!(
        value_eq_true_true_source_theorem(),
        value_eq_true_true_theorem()
    );
    assert_eq!(
        value_eq_true_false_source_theorem(),
        value_eq_true_false_theorem()
    );
    assert_eq!(value_eq_nil_source_theorem(), value_eq_nil_theorem());
    assert_eq!(
        value_eq_nil_cons_source_theorem(),
        value_eq_nil_cons_theorem(nil_cons_head, nil_cons_tail)
    );
    assert_eq!(
        value_eq_cons_nil_source_theorem(),
        value_eq_cons_nil_theorem(cons_nil_head, cons_nil_tail)
    );
    assert_eq!(
        value_eq_cons_source_theorem(),
        value_eq_cons_theorem(
            cons_left_head,
            cons_left_tail,
            cons_right_head,
            cons_right_tail,
        )
    );
    assert_eq!(
        value_kind_symbol_implies_is_symbol_source_theorem(),
        value_kind_symbol_implies_is_symbol_theorem(kind_symbol_value)
    );
    assert_eq!(
        value_kind_lambda_implies_is_lambda_source_theorem(),
        value_kind_lambda_implies_is_lambda_theorem(kind_lambda_value)
    );
    assert_eq!(
        is_symbol_true_implies_is_lambda_false_source_theorem(),
        is_symbol_true_implies_is_lambda_false_theorem(symbol_not_lambda_value)
    );
    assert_eq!(
        value_eq_comparable_symbol_source_theorem(),
        value_eq_comparable_symbol_theorem(comparable_symbol_value)
    );
    assert_eq!(
        value_eq_comparable_nil_source_theorem(),
        value_eq_comparable_nil_theorem()
    );
    assert_eq!(
        value_eq_comparable_cons_source_theorem(),
        value_eq_comparable_cons_theorem(comparable_cons_head, comparable_cons_tail)
    );
    assert_eq!(
        value_eq_true_implies_not_lambdas_source_theorem(),
        value_eq_true_implies_not_lambdas_theorem(not_lambdas_left, not_lambdas_right)
    );
    assert_eq!(
        value_non_symbol_non_lambda_is_list_source_theorem(),
        value_non_symbol_non_lambda_is_list_theorem(classified_list_value)
    );
    assert_eq!(
        value_eq_left_non_symbol_true_implies_lists_source_theorem(),
        value_eq_left_non_symbol_true_implies_lists_theorem(
            non_symbol_lists_left,
            non_symbol_lists_right,
        )
    );
    assert_eq!(
        value_eq_left_symbol_true_source_theorem(),
        value_eq_left_symbol_true_theorem(left_symbol_left, left_symbol_right)
    );
    assert_eq!(
        value_eq_left_symbol_sound_source_theorem(),
        value_eq_left_symbol_sound_theorem(left_symbol_sound_left, left_symbol_sound_right)
    );
    assert_eq!(
        value_eq_cons_true_elim_source_theorem(),
        value_eq_cons_true_elim_theorem(
            cons_elim_left_head,
            cons_elim_left_tail,
            cons_elim_right_head,
            cons_elim_right_tail,
        )
    );
    assert_eq!(
        cons_congr_source_theorem(),
        cons_congr_theorem(
            cons_congr_left_head,
            cons_congr_left_tail,
            cons_congr_right_head,
            cons_congr_right_tail,
        )
    );
    assert_eq!(
        value_eq_sound_source_theorem(),
        value_eq_sound_theorem(sound_left, sound_right)
    );
    assert_eq!(
        value_eq_refl_source_theorem(),
        value_eq_refl_theorem(refl_value)
    );
    assert_eq!(
        value_eq_true_implies_comparable_left_source_theorem(),
        value_eq_true_implies_comparable_left_theorem(comparable_left_left, comparable_left_right,)
    );
    assert_eq!(
        value_eq_true_implies_comparable_right_source_theorem(),
        value_eq_true_implies_comparable_right_theorem(
            comparable_right_left,
            comparable_right_right,
        )
    );
    assert_eq!(
        value_eq_symm_source_theorem(),
        value_eq_symm_theorem(symm_left, symm_right)
    );
}
