use super::*;

#[test]
fn bool_not_reduces_on_booleans() {
    assert_evaluates(bool_not_call(true_value()), value(false_value()));
    assert_evaluates(bool_not_call(false_value()), value(true_value()));
}

#[test]
fn bool_and_reduces_on_booleans() {
    assert_evaluates(
        bool_and_call(true_value(), true_value()),
        value(true_value()),
    );
    assert_evaluates(
        bool_and_call(true_value(), false_value()),
        value(false_value()),
    );
    assert_evaluates(
        bool_and_call(false_value(), true_value()),
        value(false_value()),
    );
}

#[test]
fn bool_or_reduces_on_booleans() {
    assert_evaluates(
        bool_or_call(true_value(), false_value()),
        value(true_value()),
    );
    assert_evaluates(
        bool_or_call(false_value(), true_value()),
        value(true_value()),
    );
    assert_evaluates(
        bool_or_call(false_value(), false_value()),
        value(false_value()),
    );
}

#[test]
fn reverse_nil_terminates_without_error() {
    assert_evaluates(reverse_call(nil()), Value::nil());
}

#[test]
fn reverse_singleton_terminates_without_error() {
    let list = singleton(quote(A));

    assert_evaluates(reverse_call(list.clone()), value(list));
}

#[test]
fn reverse_pair_terminates_without_error() {
    assert_evaluates(
        reverse_call(pair(quote(A), quote(B))),
        value(pair(quote(B), quote(A))),
    );
}

#[test]
fn reverse_triple_terminates_without_error() {
    assert_evaluates(
        reverse_call(triple(quote(A), quote(B), quote(NOT_A_LIST))),
        value(triple(quote(NOT_A_LIST), quote(B), quote(A))),
    );
}

#[test]
fn append_nil_returns_right_list() {
    let list = pair(quote(A), quote(B));

    assert_evaluates(append_call(nil(), list.clone()), value(list));
}

#[test]
fn append_pair_terminates_without_error() {
    assert_evaluates(
        append_call(pair(quote(A), quote(B)), singleton(quote(NOT_A_LIST))),
        value(triple(quote(A), quote(B), quote(NOT_A_LIST))),
    );
}

#[test]
fn append_singleton_cons_theorem_example() {
    assert_evaluates(
        append_call(singleton(quote(A)), pair(quote(B), quote(NOT_A_LIST))),
        value(triple(quote(A), quote(B), quote(NOT_A_LIST))),
    );
}

#[test]
fn append_assoc_theorem_example() {
    let left = singleton(quote(A));
    let middle = singleton(quote(B));
    let right = singleton(quote(NOT_A_LIST));
    let expected = triple(quote(A), quote(B), quote(NOT_A_LIST));

    assert_evaluates(
        append_call(append_call(left, middle), right),
        value(expected),
    );
}

#[test]
fn snoc_pair_terminates_without_error() {
    assert_evaluates(
        snoc_call(pair(quote(A), quote(B)), quote(NOT_A_LIST)),
        value(triple(quote(A), quote(B), quote(NOT_A_LIST))),
    );
}

#[test]
fn concat_list_of_lists_terminates_without_error() {
    let lists = pair(singleton(quote(A)), pair(quote(B), quote(NOT_A_LIST)));

    assert_evaluates(
        concat_call(lists),
        value(triple(quote(A), quote(B), quote(NOT_A_LIST))),
    );
}

#[test]
fn length_nil_returns_nil() {
    assert_evaluates(length_call(nil()), Value::nil());
}

#[test]
fn length_triple_returns_three() {
    assert_evaluates(
        length_call(triple(quote(A), quote(B), unit())),
        value(triple(unit(), unit(), unit())),
    );
}

#[test]
fn length_append_adds_lengths() {
    assert_evaluates(
        length_call(append_call(singleton(quote(A)), pair(quote(B), unit()))),
        value(triple(unit(), unit(), unit())),
    );
}

#[test]
fn length_map_preserves_length() {
    let constant_unit = lambda(X, unit());

    assert_evaluates(
        length_call(map_call(constant_unit, pair(quote(A), quote(B)))),
        value(pair(unit(), unit())),
    );
}

#[test]
fn take_zero_returns_nil() {
    assert_evaluates(
        take_call(nil(), triple(quote(A), quote(B), unit())),
        Value::nil(),
    );
}

#[test]
fn take_two_returns_prefix() {
    assert_evaluates(
        take_call(
            pair(unit(), unit()),
            triple(quote(A), quote(B), quote(NOT_A_LIST)),
        ),
        value(pair(quote(A), quote(B))),
    );
}

#[test]
fn take_past_end_returns_whole_list() {
    let list = pair(quote(A), quote(B));

    assert_evaluates(
        take_call(triple(unit(), unit(), unit()), list.clone()),
        value(list),
    );
}

#[test]
fn drop_zero_returns_input() {
    let list = triple(quote(A), quote(B), unit());

    assert_evaluates(drop_call(nil(), list.clone()), value(list));
}

#[test]
fn drop_two_returns_suffix() {
    assert_evaluates(
        drop_call(
            pair(unit(), unit()),
            triple(quote(A), quote(B), quote(NOT_A_LIST)),
        ),
        value(singleton(quote(NOT_A_LIST))),
    );
}

#[test]
fn drop_past_end_returns_nil() {
    assert_evaluates(
        drop_call(triple(unit(), unit(), unit()), pair(quote(A), quote(B))),
        Value::nil(),
    );
}

#[test]
fn split_at_zero_returns_empty_prefix_and_input_suffix() {
    let list = triple(quote(A), quote(B), unit());

    assert_evaluates(split_at_call(nil(), list.clone()), value(pair(nil(), list)));
}

#[test]
fn split_at_two_returns_prefix_and_suffix() {
    assert_evaluates(
        split_at_call(
            pair(unit(), unit()),
            triple(quote(A), quote(B), quote(NOT_A_LIST)),
        ),
        value(pair(pair(quote(A), quote(B)), singleton(quote(NOT_A_LIST)))),
    );
}

#[test]
fn split_at_past_end_returns_input_prefix_and_empty_suffix() {
    let list = pair(quote(A), quote(B));

    assert_evaluates(
        split_at_call(triple(unit(), unit(), unit()), list.clone()),
        value(pair(list, nil())),
    );
}

#[test]
fn option_primitives_encode_none_and_some() {
    assert_evaluates(none(), Value::quote(prelude_symbol(":none")));
    assert_evaluates(
        some_call(quote(A)),
        value(pair(quote(prelude_symbol(":some")), quote(A))),
    );
    assert_evaluates(is_none_call(none()), Value::quote(prelude_symbol(":true")));
    assert_evaluates(
        is_none_call(some_call(quote(A))),
        Value::quote(prelude_symbol(":false")),
    );
    assert_evaluates(is_some_call(none()), Value::quote(prelude_symbol(":false")));
    assert_evaluates(
        is_some_call(some_call(quote(A))),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn is_some_rejects_malformed_some_lists() {
    assert_evaluates(
        is_some_call(singleton(quote(prelude_symbol(":some")))),
        Value::quote(prelude_symbol(":false")),
    );
    assert_evaluates(
        is_some_call(triple(quote(prelude_symbol(":some")), quote(A), quote(B))),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn nth_returns_some_at_index() {
    assert_evaluates(
        nth_call(
            pair(unit(), unit()),
            triple(quote(A), quote(B), quote(NOT_A_LIST)),
        ),
        value(pair(quote(prelude_symbol(":some")), quote(NOT_A_LIST))),
    );
}

#[test]
fn nth_returns_none_when_out_of_bounds() {
    assert_evaluates(
        nth_call(triple(unit(), unit(), unit()), pair(quote(A), quote(B))),
        Value::quote(prelude_symbol(":none")),
    );
}

#[test]
fn append_take_drop_rebuilds_list() {
    let count = pair(unit(), unit());
    let list = triple(quote(A), quote(B), quote(NOT_A_LIST));

    assert_evaluates(
        append_call(
            take_call(count.clone(), list.clone()),
            drop_call(count, list.clone()),
        ),
        value(list),
    );
}

#[test]
fn replicate_zero_returns_nil() {
    assert_evaluates(replicate_call(nil(), quote(A)), Value::nil());
}

#[test]
fn replicate_three_repeats_value() {
    assert_evaluates(
        replicate_call(triple(unit(), unit(), unit()), quote(A)),
        value(triple(quote(A), quote(A), quote(A))),
    );
}

#[test]
fn replicate_uses_count_spine_not_count_elements() {
    assert_evaluates(
        replicate_call(pair(quote(A), quote(B)), unit()),
        value(pair(unit(), unit())),
    );
}

#[test]
fn length_replicate_matches_count_length() {
    let count = pair(quote(A), quote(B));

    assert_evaluates(
        length_call(replicate_call(count, unit())),
        value(pair(unit(), unit())),
    );
}

#[test]
fn intersperse_nil_returns_nil() {
    assert_evaluates(intersperse_call(unit(), nil()), Value::nil());
}

#[test]
fn intersperse_singleton_returns_same_list() {
    let list = singleton(quote(A));

    assert_evaluates(intersperse_call(unit(), list.clone()), value(list));
}

#[test]
fn intersperse_triple_inserts_separator_between_elements() {
    assert_evaluates(
        intersperse_call(unit(), triple(quote(A), quote(B), quote(NOT_A_LIST))),
        value(cons(
            quote(A),
            cons(
                unit(),
                cons(quote(B), cons(unit(), singleton(quote(NOT_A_LIST)))),
            ),
        )),
    );
}

#[test]
fn intercalate_nil_returns_nil() {
    assert_evaluates(intercalate_call(singleton(unit()), nil()), Value::nil());
}

#[test]
fn intercalate_singleton_returns_only_list() {
    let list = pair(quote(A), quote(B));

    assert_evaluates(
        intercalate_call(singleton(unit()), singleton(list.clone())),
        value(list),
    );
}

#[test]
fn intercalate_triple_inserts_separator_between_lists() {
    let lists = triple(
        singleton(quote(A)),
        pair(quote(B), quote(NOT_A_LIST)),
        singleton(quote(B)),
    );
    let expected = cons(
        quote(A),
        cons(
            unit(),
            cons(
                quote(B),
                cons(quote(NOT_A_LIST), cons(unit(), singleton(quote(B)))),
            ),
        ),
    );

    assert_evaluates(intercalate_call(singleton(unit()), lists), value(expected));
}

#[test]
fn all_lists_nil_returns_true() {
    assert_evaluates(all_lists_call(nil()), Value::quote(prelude_symbol(":true")));
}

#[test]
fn all_lists_accepts_lists_of_lists() {
    assert_evaluates(
        all_lists_call(pair(singleton(quote(A)), pair(quote(B), quote(NOT_A_LIST)))),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn all_lists_rejects_non_list_elements() {
    assert_evaluates(
        all_lists_call(pair(singleton(quote(A)), quote(B))),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn map_nil_returns_nil() {
    let identity = lambda(X, var(X));

    assert_evaluates(map_call(identity, nil()), Value::nil());
}

#[test]
fn map_identity_returns_same_list() {
    let identity = lambda(X, var(X));

    assert_evaluates(
        map_call(identity, triple(quote(A), quote(B), quote(NOT_A_LIST))),
        value(triple(quote(A), quote(B), quote(NOT_A_LIST))),
    );
}

#[test]
fn map_constant_returns_constant_list() {
    let constant_unit = lambda(X, unit());

    assert_evaluates(
        map_call(constant_unit, pair(quote(A), quote(B))),
        value(pair(unit(), unit())),
    );
}

#[test]
fn concat_map_nil_returns_nil() {
    let singleton_function = lambda(X, singleton(var(X)));

    assert_evaluates(concat_map_call(singleton_function, nil()), Value::nil());
}

#[test]
fn concat_map_singleton_function_flattens() {
    let singleton_function = lambda(X, singleton(var(X)));

    assert_evaluates(
        concat_map_call(singleton_function, pair(quote(A), quote(B))),
        value(pair(quote(A), quote(B))),
    );
}

#[test]
fn concat_map_pair_function_flattens() {
    let pair_function = lambda(X, pair(var(X), var(X)));
    let expected = cons(quote(A), cons(quote(A), pair(quote(B), quote(B))));

    assert_evaluates(
        concat_map_call(pair_function, pair(quote(A), quote(B))),
        value(expected),
    );
}

#[test]
fn fold_right_nil_returns_initial() {
    let cons_function = lambda(X, lambda(ACCUMULATOR, cons(var(X), var(ACCUMULATOR))));

    assert_evaluates(fold_right_call(cons_function, nil(), nil()), Value::nil());
}

#[test]
fn fold_right_cons_function_rebuilds_list() {
    let cons_function = lambda(X, lambda(ACCUMULATOR, cons(var(X), var(ACCUMULATOR))));

    assert_evaluates(
        fold_right_call(cons_function, nil(), triple(quote(A), quote(B), unit())),
        value(triple(quote(A), quote(B), unit())),
    );
}

#[test]
fn fold_right_accumulator_function_returns_initial() {
    let accumulator_function = lambda(X, lambda(ACCUMULATOR, var(ACCUMULATOR)));

    assert_evaluates(
        fold_right_call(accumulator_function, unit(), pair(quote(A), quote(B))),
        Value::quote(prelude_symbol("unit")),
    );
}

#[test]
fn fold_left_nil_returns_initial() {
    let accumulator_function = lambda(ACCUMULATOR, lambda(X, var(ACCUMULATOR)));

    assert_evaluates(
        fold_left_call(accumulator_function, unit(), nil()),
        Value::quote(prelude_symbol("unit")),
    );
}

#[test]
fn fold_left_front_cons_reverses_list() {
    let front_cons = fold_left_reverse_function(ACCUMULATOR, X);

    assert_evaluates(
        fold_left_call(front_cons, nil(), triple(quote(A), quote(B), unit())),
        value(triple(unit(), quote(B), quote(A))),
    );
}

#[test]
fn fold_left_front_cons_with_accumulates_prefix() {
    let front_cons = fold_left_reverse_function(ACCUMULATOR, X);

    assert_evaluates(
        fold_left_call(front_cons, singleton(unit()), pair(quote(A), quote(B))),
        value(triple(quote(B), quote(A), unit())),
    );
}

#[test]
fn zip_left_nil_returns_nil() {
    assert_evaluates(zip_call(nil(), pair(quote(A), quote(B))), Value::nil());
}

#[test]
fn zip_right_nil_returns_nil() {
    assert_evaluates(zip_call(pair(quote(A), quote(B)), nil()), Value::nil());
}

#[test]
fn zip_truncates_to_shorter_list() {
    let expected = pair(pair(quote(A), unit()), pair(quote(B), quote(A)));

    assert_evaluates(
        zip_call(
            triple(quote(A), quote(B), quote(NOT_A_LIST)),
            pair(unit(), quote(A)),
        ),
        value(expected),
    );
}

#[test]
fn unzip_nil_returns_pair_of_nil() {
    assert_evaluates(unzip_call(nil()), value(pair(nil(), nil())));
}

#[test]
fn unzip_splits_list_of_pairs() {
    let pairs = pair(pair(quote(A), unit()), pair(quote(B), quote(A)));
    let expected = pair(pair(quote(A), quote(B)), pair(unit(), quote(A)));

    assert_evaluates(unzip_call(pairs), value(expected));
}

#[test]
fn unzip_non_pair_head_errors() {
    assert_evaluates(
        unzip_call(singleton(quote(A))),
        Effect::error(RUNTIME_ERROR),
    );
}

#[test]
fn zip_with_left_nil_returns_nil() {
    let pair_function = lambda(X, lambda(NEXT, pair(var(X), var(NEXT))));

    assert_evaluates(
        zip_with_call(pair_function, nil(), pair(quote(A), quote(B))),
        Value::nil(),
    );
}

#[test]
fn zip_with_right_nil_returns_nil() {
    let pair_function = lambda(X, lambda(NEXT, pair(var(X), var(NEXT))));

    assert_evaluates(
        zip_with_call(pair_function, pair(quote(A), quote(B)), nil()),
        Value::nil(),
    );
}

#[test]
fn zip_with_pair_function_truncates_to_shorter_list() {
    let pair_function = lambda(X, lambda(NEXT, pair(var(X), var(NEXT))));
    let expected = pair(pair(quote(A), unit()), pair(quote(B), quote(A)));

    assert_evaluates(
        zip_with_call(
            pair_function,
            triple(quote(A), quote(B), quote(NOT_A_LIST)),
            pair(unit(), quote(A)),
        ),
        value(expected),
    );
}

fn always_true_predicate() -> Computation {
    lambda(X, true_value())
}

fn always_false_predicate() -> Computation {
    lambda(X, false_value())
}

fn is_a_predicate() -> Computation {
    lambda(X, crate::symbol_eq(var(X), quote(A)))
}

#[test]
fn filter_nil_returns_nil() {
    assert_evaluates(filter_call(always_true_predicate(), nil()), Value::nil());
}

#[test]
fn filter_true_predicate_keeps_everything() {
    let list = triple(quote(A), quote(B), unit());

    assert_evaluates(
        filter_call(always_true_predicate(), list.clone()),
        value(list),
    );
}

#[test]
fn filter_false_predicate_drops_everything() {
    assert_evaluates(
        filter_call(always_false_predicate(), triple(quote(A), quote(B), unit())),
        Value::nil(),
    );
}

#[test]
fn filter_symbol_eq_keeps_matching_symbols() {
    assert_evaluates(
        filter_call(is_a_predicate(), triple(quote(A), quote(B), quote(A))),
        value(pair(quote(A), quote(A))),
    );
}

#[test]
fn partition_nil_returns_pair_of_nil() {
    assert_evaluates(
        partition_call(always_true_predicate(), nil()),
        value(pair(nil(), nil())),
    );
}

#[test]
fn partition_true_predicate_puts_everything_on_left() {
    let list = pair(quote(A), quote(B));

    assert_evaluates(
        partition_call(always_true_predicate(), list.clone()),
        value(pair(list, nil())),
    );
}

#[test]
fn partition_false_predicate_puts_everything_on_right() {
    let list = pair(quote(A), quote(B));

    assert_evaluates(
        partition_call(always_false_predicate(), list.clone()),
        value(pair(nil(), list)),
    );
}

#[test]
fn partition_symbol_eq_splits_matching_and_missing_values() {
    assert_evaluates(
        partition_call(is_a_predicate(), triple(quote(A), quote(B), quote(A))),
        value(pair(pair(quote(A), quote(A)), singleton(quote(B)))),
    );
}

#[test]
fn any_nil_returns_false() {
    assert_evaluates(
        any_call(always_true_predicate(), nil()),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn any_symbol_eq_returns_true_when_match_exists() {
    assert_evaluates(
        any_call(is_a_predicate(), triple(quote(B), quote(A), unit())),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn any_symbol_eq_returns_false_when_no_match() {
    assert_evaluates(
        any_call(is_a_predicate(), pair(quote(B), unit())),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn all_nil_returns_true() {
    assert_evaluates(
        all_call(always_false_predicate(), nil()),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn all_symbol_eq_returns_true_when_all_match() {
    assert_evaluates(
        all_call(is_a_predicate(), pair(quote(A), quote(A))),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn all_symbol_eq_returns_false_when_any_missing() {
    assert_evaluates(
        all_call(is_a_predicate(), triple(quote(A), quote(B), quote(A))),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn find_nil_returns_none() {
    assert_evaluates(
        find_call(is_a_predicate(), nil()),
        Value::quote(prelude_symbol(":none")),
    );
}

#[test]
fn find_returns_first_matching_value() {
    assert_evaluates(
        find_call(is_a_predicate(), triple(quote(B), quote(A), quote(A))),
        value(pair(quote(prelude_symbol(":some")), quote(A))),
    );
}

#[test]
fn find_returns_none_for_miss() {
    assert_evaluates(
        find_call(is_a_predicate(), pair(quote(B), unit())),
        Value::quote(prelude_symbol(":none")),
    );
}

#[test]
fn elem_index_nil_returns_none() {
    assert_evaluates(
        elem_index_call(quote(A), nil()),
        Value::quote(prelude_symbol(":none")),
    );
}

#[test]
fn elem_index_returns_zero_for_head_match() {
    assert_evaluates(
        elem_index_call(quote(A), pair(quote(A), quote(B))),
        value(pair(quote(prelude_symbol(":some")), nil())),
    );
}

#[test]
fn elem_index_returns_first_matching_index() {
    assert_evaluates(
        elem_index_call(quote(A), triple(quote(B), quote(B), quote(A))),
        value(pair(quote(prelude_symbol(":some")), pair(unit(), unit()))),
    );
}

#[test]
fn elem_index_returns_none_for_miss() {
    assert_evaluates(
        elem_index_call(quote(A), pair(quote(B), unit())),
        Value::quote(prelude_symbol(":none")),
    );
}

#[test]
fn is_symbol_returns_true_for_symbols() {
    assert_evaluates(
        is_symbol_call(quote(A)),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn is_symbol_returns_false_for_lists_and_lambdas() {
    assert_evaluates(
        is_symbol_call(nil()),
        Value::quote(prelude_symbol(":false")),
    );
    assert_evaluates(
        is_symbol_call(lambda(X, var(X))),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn is_lambda_returns_true_for_lambdas() {
    assert_evaluates(
        is_lambda_call(lambda(X, var(X))),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn is_lambda_returns_false_for_symbols_and_lists() {
    assert_evaluates(
        is_lambda_call(quote(A)),
        Value::quote(prelude_symbol(":false")),
    );
    assert_evaluates(
        is_lambda_call(nil()),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn is_list_value_returns_true_for_nil_and_cons() {
    assert_evaluates(
        is_list_value_call(nil()),
        Value::quote(prelude_symbol(":true")),
    );
    assert_evaluates(
        is_list_value_call(singleton(quote(A))),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn is_list_value_returns_false_for_symbols_and_lambdas() {
    assert_evaluates(
        is_list_value_call(quote(A)),
        Value::quote(prelude_symbol(":false")),
    );
    assert_evaluates(
        is_list_value_call(lambda(X, var(X))),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn value_eq_symbol_same_returns_true() {
    assert_evaluates(
        value_eq_call(quote(A), quote(A)),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn value_eq_symbol_different_returns_false() {
    assert_evaluates(
        value_eq_call(quote(A), quote(B)),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn value_eq_symbol_list_mismatch_returns_false() {
    assert_evaluates(
        value_eq_call(quote(A), singleton(quote(A))),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn value_eq_nil_nil_returns_true() {
    assert_evaluates(
        value_eq_call(nil(), nil()),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn value_eq_nil_cons_returns_false() {
    assert_evaluates(
        value_eq_call(nil(), singleton(quote(A))),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn value_eq_cons_nil_returns_false() {
    assert_evaluates(
        value_eq_call(singleton(quote(A)), nil()),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn value_eq_equal_cons_returns_true() {
    assert_evaluates(
        value_eq_call(pair(quote(A), quote(B)), pair(quote(A), quote(B))),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn value_eq_nested_lists_returns_true() {
    let left = pair(singleton(quote(A)), pair(quote(B), nil()));
    let right = pair(singleton(quote(A)), pair(quote(B), nil()));

    assert_evaluates(
        value_eq_call(left, right),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn value_eq_nested_lists_detect_difference() {
    let left = pair(singleton(quote(A)), pair(quote(B), nil()));
    let right = pair(singleton(quote(A)), pair(quote(A), nil()));

    assert_evaluates(
        value_eq_call(left, right),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn value_eq_lambda_left_errors() {
    assert_evaluates(
        value_eq_call(lambda(X, var(X)), quote(A)),
        Effect::error(RUNTIME_ERROR),
    );
}

#[test]
fn value_eq_lambda_right_errors() {
    assert_evaluates(
        value_eq_call(quote(A), lambda(X, var(X))),
        Effect::error(RUNTIME_ERROR),
    );
}

#[test]
fn value_eq_cons_lambda_head_errors() {
    assert_evaluates(
        value_eq_call(singleton(lambda(X, var(X))), singleton(lambda(X, var(X)))),
        Effect::error(RUNTIME_ERROR),
    );
}

#[test]
fn value_eq_short_circuits_tail_after_head_difference() {
    let left = pair(quote(A), lambda(X, var(X)));
    let right = pair(quote(B), lambda(X, var(X)));

    assert_evaluates(
        value_eq_call(left, right),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn value_eq_comparable_accepts_symbols_and_lambda_free_lists() {
    assert_evaluates(
        value_eq_comparable_call(quote(A)),
        Value::quote(prelude_symbol(":true")),
    );
    assert_evaluates(
        value_eq_comparable_call(pair(quote(A), quote(B))),
        Value::quote(prelude_symbol(":true")),
    );
    assert_evaluates(
        value_eq_comparable_call(pair(singleton(quote(A)), pair(quote(B), nil()))),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn value_eq_comparable_rejects_lambdas_even_nested() {
    assert_evaluates(
        value_eq_comparable_call(lambda(X, var(X))),
        Value::quote(prelude_symbol(":false")),
    );
    assert_evaluates(
        value_eq_comparable_call(singleton(lambda(X, var(X)))),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn member_nil_returns_false() {
    assert_evaluates(
        member_call(quote(A), nil()),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn member_returns_true_for_head_match() {
    assert_evaluates(
        member_call(quote(A), triple(quote(A), quote(B), unit())),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn member_returns_true_for_tail_match() {
    assert_evaluates(
        member_call(quote(A), triple(quote(B), unit(), quote(A))),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn member_returns_false_for_miss() {
    assert_evaluates(
        member_call(quote(A), pair(quote(B), unit())),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn member_matches_nested_list_values() {
    assert_evaluates(
        member_call(
            singleton(quote(A)),
            pair(singleton(quote(B)), singleton(quote(A))),
        ),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn member_lambda_target_errors() {
    assert_evaluates(
        member_call(lambda(X, var(X)), singleton(quote(A))),
        Effect::error(RUNTIME_ERROR),
    );
}

#[test]
fn member_lambda_head_errors() {
    assert_evaluates(
        member_call(quote(A), singleton(lambda(X, var(X)))),
        Effect::error(RUNTIME_ERROR),
    );
}

#[test]
fn member_short_circuits_tail_after_head_match() {
    assert_evaluates(
        member_call(quote(A), pair(quote(A), lambda(X, var(X)))),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn last_nil_reduces_to_error() {
    assert_evaluates(last_call(nil()), Effect::error(RUNTIME_ERROR));
}

#[test]
fn last_singleton_returns_value() {
    assert_evaluates(last_call(singleton(quote(A))), Value::quote(A));
}

#[test]
fn last_triple_returns_final_value() {
    assert_evaluates(
        last_call(triple(quote(A), quote(B), quote(NOT_A_LIST))),
        Value::quote(NOT_A_LIST),
    );
}

#[test]
fn init_nil_reduces_to_error() {
    assert_evaluates(init_call(nil()), Effect::error(RUNTIME_ERROR));
}

#[test]
fn init_singleton_returns_nil() {
    assert_evaluates(init_call(singleton(quote(A))), Value::nil());
}

#[test]
fn init_triple_returns_prefix() {
    assert_evaluates(
        init_call(triple(quote(A), quote(B), quote(NOT_A_LIST))),
        value(pair(quote(A), quote(B))),
    );
}

#[test]
fn null_nil_returns_true() {
    assert_evaluates(null_call(nil()), Value::quote(prelude_symbol(":true")));
}

#[test]
fn null_cons_returns_false() {
    assert_evaluates(
        null_call(singleton(quote(A))),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn is_singleton_nil_returns_false() {
    assert_evaluates(
        is_singleton_call(nil()),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn is_singleton_singleton_returns_true() {
    assert_evaluates(
        is_singleton_call(singleton(quote(A))),
        Value::quote(prelude_symbol(":true")),
    );
}

#[test]
fn is_singleton_pair_returns_false() {
    assert_evaluates(
        is_singleton_call(pair(quote(A), quote(B))),
        Value::quote(prelude_symbol(":false")),
    );
}

#[test]
fn loop_forever_diverges() {
    let theory = crate::prelude::theory();
    let computation = loop_forever_call();
    let proof = prove_evaluation(computation.clone(), Effect::diverge());

    assert!(theory.check(&proof, &diverges(computation)));
}

#[test]
fn reverse_non_list_input_reduces_to_error() {
    assert_evaluates(
        reverse_call(quote(NOT_A_LIST)),
        Effect::error(RUNTIME_ERROR),
    );
}

#[test]
fn reverse_malformed_tail_reduces_to_error() {
    assert_evaluates(
        reverse_call(cons(quote(A), quote(NOT_A_LIST))),
        Effect::error(RUNTIME_ERROR),
    );
}

#[test]
fn evaluation_proof_rejects_wrong_expected_value() {
    assert_eq!(
        proof_by_evaluation(reverse_call(nil()), Value::quote(NOT_A_LIST), 64),
        Err(EvaluationProofError::UnexpectedNormalForm {
            expected: quote(NOT_A_LIST),
            actual: nil(),
        })
    );
}
