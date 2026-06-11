use super::*;

#[test]
fn filter_any_all_source_theorems_have_expected_shape() {
    let filter_nil_predicate = theorem_symbol("filter_nil", "predicate");
    let filter_true_predicate = theorem_symbol("filter_cons_true", "predicate");
    let filter_true_head = theorem_symbol("filter_cons_true", "head");
    let filter_true_tail = theorem_symbol("filter_cons_true", "tail");
    let filter_false_predicate = theorem_symbol("filter_cons_false", "predicate");
    let filter_false_head = theorem_symbol("filter_cons_false", "head");
    let filter_false_tail = theorem_symbol("filter_cons_false", "tail");
    let filter_computes_predicate = theorem_symbol("filter_computes_to_list", "predicate");
    let filter_computes_value = theorem_symbol("filter_computes_to_list", "value");
    let filter_computes_list = theorem_symbol("filter_computes_to_list", "list");
    let filter_computes_result = theorem_symbol("filter_computes_to_list", "result");

    assert_eq!(
        filter_nil_source_theorem(),
        filter_nil_theorem(filter_nil_predicate)
    );
    assert_eq!(
        filter_cons_true_source_theorem(),
        filter_cons_true_theorem(filter_true_predicate, filter_true_head, filter_true_tail)
    );
    assert_eq!(
        filter_cons_false_source_theorem(),
        filter_cons_false_theorem(filter_false_predicate, filter_false_head, filter_false_tail)
    );
    assert_eq!(
        filter_computes_to_list_source_theorem(),
        filter_computes_to_list_theorem(
            filter_computes_predicate,
            filter_computes_value,
            filter_computes_list,
            filter_computes_result,
        )
    );

    let partition_nil_predicate = theorem_symbol("partition_nil", "predicate");
    let partition_true_predicate = theorem_symbol("partition_cons_true", "predicate");
    let partition_true_head = theorem_symbol("partition_cons_true", "head");
    let partition_true_tail = theorem_symbol("partition_cons_true", "tail");
    let partition_false_predicate = theorem_symbol("partition_cons_false", "predicate");
    let partition_false_head = theorem_symbol("partition_cons_false", "head");
    let partition_false_tail = theorem_symbol("partition_cons_false", "tail");

    assert_eq!(
        partition_nil_source_theorem(),
        partition_nil_theorem(partition_nil_predicate)
    );
    assert_eq!(
        partition_cons_true_source_theorem(),
        partition_cons_true_theorem(
            partition_true_predicate,
            partition_true_head,
            partition_true_tail,
        )
    );
    assert_eq!(
        partition_cons_false_source_theorem(),
        partition_cons_false_theorem(
            partition_false_predicate,
            partition_false_head,
            partition_false_tail,
        )
    );

    let any_nil_predicate = theorem_symbol("any_nil", "predicate");
    let any_true_predicate = theorem_symbol("any_cons_true", "predicate");
    let any_true_head = theorem_symbol("any_cons_true", "head");
    let any_true_tail = theorem_symbol("any_cons_true", "tail");
    let any_false_predicate = theorem_symbol("any_cons_false", "predicate");
    let any_false_head = theorem_symbol("any_cons_false", "head");
    let any_false_tail = theorem_symbol("any_cons_false", "tail");
    let any_computes_predicate = theorem_symbol("any_computes_to_bool", "predicate");
    let any_computes_value = theorem_symbol("any_computes_to_bool", "value");
    let any_computes_list = theorem_symbol("any_computes_to_bool", "list");

    assert_eq!(any_nil_source_theorem(), any_nil_theorem(any_nil_predicate));
    assert_eq!(
        any_cons_true_source_theorem(),
        any_cons_true_theorem(any_true_predicate, any_true_head, any_true_tail)
    );
    assert_eq!(
        any_cons_false_source_theorem(),
        any_cons_false_theorem(any_false_predicate, any_false_head, any_false_tail)
    );
    assert_eq!(
        any_computes_to_bool_source_theorem(),
        any_computes_to_bool_theorem(
            any_computes_predicate,
            any_computes_value,
            any_computes_list,
        )
    );

    let member_nil_value = theorem_symbol("member_nil", "value");
    let member_true_value = theorem_symbol("member_cons_true", "value");
    let member_true_head = theorem_symbol("member_cons_true", "head");
    let member_true_tail = theorem_symbol("member_cons_true", "tail");
    let member_false_value = theorem_symbol("member_cons_false", "value");
    let member_false_head = theorem_symbol("member_cons_false", "head");
    let member_false_tail = theorem_symbol("member_cons_false", "tail");

    assert_eq!(
        member_nil_source_theorem(),
        member_nil_theorem(member_nil_value)
    );
    assert_eq!(
        member_cons_true_source_theorem(),
        member_cons_true_theorem(member_true_value, member_true_head, member_true_tail)
    );
    assert_eq!(
        member_cons_false_source_theorem(),
        member_cons_false_theorem(member_false_value, member_false_head, member_false_tail)
    );

    let all_nil_predicate = theorem_symbol("all_nil", "predicate");
    let all_true_predicate = theorem_symbol("all_cons_true", "predicate");
    let all_true_head = theorem_symbol("all_cons_true", "head");
    let all_true_tail = theorem_symbol("all_cons_true", "tail");
    let all_false_predicate = theorem_symbol("all_cons_false", "predicate");
    let all_false_head = theorem_symbol("all_cons_false", "head");
    let all_false_tail = theorem_symbol("all_cons_false", "tail");
    let all_computes_predicate = theorem_symbol("all_computes_to_bool", "predicate");
    let all_computes_value = theorem_symbol("all_computes_to_bool", "value");
    let all_computes_list = theorem_symbol("all_computes_to_bool", "list");

    assert_eq!(all_nil_source_theorem(), all_nil_theorem(all_nil_predicate));
    assert_eq!(
        all_cons_true_source_theorem(),
        all_cons_true_theorem(all_true_predicate, all_true_head, all_true_tail)
    );
    assert_eq!(
        all_cons_false_source_theorem(),
        all_cons_false_theorem(all_false_predicate, all_false_head, all_false_tail)
    );
    assert_eq!(
        all_computes_to_bool_source_theorem(),
        all_computes_to_bool_theorem(
            all_computes_predicate,
            all_computes_value,
            all_computes_list,
        )
    );

    let find_nil_predicate = theorem_symbol("find_nil", "predicate");
    let find_true_predicate = theorem_symbol("find_cons_true", "predicate");
    let find_true_head = theorem_symbol("find_cons_true", "head");
    let find_true_tail = theorem_symbol("find_cons_true", "tail");
    let find_false_predicate = theorem_symbol("find_cons_false", "predicate");
    let find_false_head = theorem_symbol("find_cons_false", "head");
    let find_false_tail = theorem_symbol("find_cons_false", "tail");
    let find_append_predicate = theorem_symbol("find_append", "predicate");
    let find_append_value = theorem_symbol("find_append", "value");
    let find_append_left = theorem_symbol("find_append", "left");
    let find_append_right = theorem_symbol("find_append", "right");

    assert_eq!(
        find_nil_source_theorem(),
        find_nil_theorem(find_nil_predicate)
    );
    assert_eq!(
        find_cons_true_source_theorem(),
        find_cons_true_theorem(find_true_predicate, find_true_head, find_true_tail)
    );
    assert_eq!(
        find_cons_false_source_theorem(),
        find_cons_false_theorem(find_false_predicate, find_false_head, find_false_tail)
    );
    assert_eq!(
        find_append_source_theorem(),
        find_append_theorem(
            find_append_predicate,
            find_append_value,
            find_append_left,
            find_append_right,
        )
    );

    let elem_index_nil_value = theorem_symbol("elem_index_nil", "value");
    let elem_index_true_value = theorem_symbol("elem_index_cons_true", "value");
    let elem_index_true_head = theorem_symbol("elem_index_cons_true", "head");
    let elem_index_true_tail = theorem_symbol("elem_index_cons_true", "tail");
    let elem_index_none_value = theorem_symbol("elem_index_cons_false_none", "value");
    let elem_index_none_head = theorem_symbol("elem_index_cons_false_none", "head");
    let elem_index_none_tail = theorem_symbol("elem_index_cons_false_none", "tail");
    let elem_index_some_value = theorem_symbol("elem_index_cons_false_some", "value");
    let elem_index_some_head = theorem_symbol("elem_index_cons_false_some", "head");
    let elem_index_some_tail = theorem_symbol("elem_index_cons_false_some", "tail");
    let elem_index_some_index = theorem_symbol("elem_index_cons_false_some", "index");

    assert_eq!(
        elem_index_nil_source_theorem(),
        elem_index_nil_theorem(elem_index_nil_value)
    );
    assert_eq!(
        elem_index_cons_true_source_theorem(),
        elem_index_cons_true_theorem(
            elem_index_true_value,
            elem_index_true_head,
            elem_index_true_tail,
        )
    );
    assert_eq!(
        elem_index_cons_false_none_source_theorem(),
        elem_index_cons_false_none_theorem(
            elem_index_none_value,
            elem_index_none_head,
            elem_index_none_tail,
        )
    );
    assert_eq!(
        elem_index_cons_false_some_source_theorem(),
        elem_index_cons_false_some_theorem(
            elem_index_some_value,
            elem_index_some_head,
            elem_index_some_tail,
            elem_index_some_index,
        )
    );
}

#[test]
fn higher_order_relation_source_theorems_have_expected_shape() {
    assert_alpha_eq(
        &map_identity_source_theorem(),
        &map_identity_theorem(X, VALUE),
    );
    assert_alpha_eq(
        &concat_map_singleton_source_theorem(),
        &concat_map_singleton_theorem(X, VALUE),
    );
    assert_eq!(
        option_map_nth_source_theorem(),
        option_map_nth_theorem(
            theorem_symbol("option_map_nth", "function"),
            theorem_symbol("option_map_nth", "value"),
            theorem_symbol("option_map_nth", "mapped_value"),
            theorem_symbol("option_map_nth", "index"),
            theorem_symbol("option_map_nth", "list"),
        )
    );
    assert_eq!(
        concat_map_as_concat_map_source_theorem(),
        concat_map_as_concat_map_theorem(
            theorem_symbol("concat_map_as_concat_map", "function"),
            theorem_symbol("concat_map_as_concat_map", "value"),
            theorem_symbol("concat_map_as_concat_map", "mapped_list"),
            theorem_symbol("concat_map_as_concat_map", "list"),
        )
    );
    assert_alpha_eq(
        &fold_right_cons_nil_source_theorem(),
        &fold_right_cons_nil_theorem(X, VALUE, ACCUMULATOR),
    );
    assert_eq!(
        fold_right_append_source_theorem(),
        fold_right_append_theorem(
            theorem_symbol("fold_right_append", "function"),
            theorem_symbol("fold_right_append", "initial"),
            theorem_symbol("fold_right_append", "value"),
            theorem_symbol("fold_right_append", "accumulator"),
            theorem_symbol("fold_right_append", "folded_value"),
            theorem_symbol("fold_right_append", "left"),
            theorem_symbol("fold_right_append", "right"),
        )
    );
    assert_eq!(
        fold_left_append_source_theorem(),
        fold_left_append_theorem(
            theorem_symbol("fold_left_append", "function"),
            theorem_symbol("fold_left_append", "accumulator"),
            theorem_symbol("fold_left_append", "value"),
            theorem_symbol("fold_left_append", "folded_value"),
            theorem_symbol("fold_left_append", "left"),
            theorem_symbol("fold_left_append", "initial"),
            theorem_symbol("fold_left_append", "right"),
        )
    );
    assert_alpha_eq(
        &fold_right_map_source_theorem(),
        &fold_right_map_theorem(
            FUNCTION,
            RIGHT_VALUE,
            INITIAL,
            VALUE,
            MAPPED_VALUE,
            LEFT_VALUE,
            ACCUMULATOR,
            FOLDED_VALUE,
            X,
            HEAD,
            TAIL,
        ),
    );
    assert_alpha_eq(
        &fold_left_map_source_theorem(),
        &fold_left_map_theorem(
            FUNCTION,
            RIGHT_VALUE,
            VALUE,
            MAPPED_VALUE,
            ACCUMULATOR,
            LEFT_VALUE,
            FOLDED_VALUE,
            X,
            INITIAL,
            HEAD,
            TAIL,
        ),
    );
    assert_alpha_eq(
        &fold_left_reverse_acc_source_theorem(),
        &fold_left_reverse_acc_theorem(X, ACCUMULATOR, INITIAL, VALUE),
    );
    assert_alpha_eq(
        &fold_left_reverse_source_theorem(),
        &fold_left_reverse_theorem(X, ACCUMULATOR, VALUE),
    );
}

#[test]
fn last_theorems_have_expected_shape() {
    assert_eq!(
        last_nil_errors_theorem(),
        errors_with(last_call(nil()), RUNTIME_ERROR)
    );
    assert_eq!(
        last_singleton_theorem(HEAD),
        forall_where(
            HEAD,
            is_value(var(HEAD)),
            computes_to(last_call(singleton(var(HEAD))), var(HEAD)),
        )
    );
    assert_eq!(
        last_cons_theorem(HEAD, NEXT, TAIL),
        forall_where(
            HEAD,
            is_value(var(HEAD)),
            forall_where(
                NEXT,
                is_value(var(NEXT)),
                forall_where(
                    TAIL,
                    is_list(var(TAIL)),
                    computes_to(
                        last_call(cons(var(HEAD), cons(var(NEXT), var(TAIL)))),
                        last_call(cons(var(NEXT), var(TAIL))),
                    ),
                ),
            ),
        )
    );
}

#[test]
fn last_source_theorems_have_expected_shape() {
    let singleton_head = theorem_symbol("last_singleton", "head");
    let cons_head = theorem_symbol("last_cons", "head");
    let cons_next = theorem_symbol("last_cons", "next");
    let cons_tail = theorem_symbol("last_cons", "tail");

    assert_eq!(last_nil_errors_source_theorem(), last_nil_errors_theorem());
    assert_eq!(
        last_singleton_source_theorem(),
        last_singleton_theorem(singleton_head)
    );
    assert_eq!(
        last_cons_source_theorem(),
        last_cons_theorem(cons_head, cons_next, cons_tail)
    );
}

#[test]
fn init_theorems_have_expected_shape() {
    assert_eq!(
        init_nil_errors_theorem(),
        errors_with(init_call(nil()), RUNTIME_ERROR)
    );
    assert_eq!(
        init_singleton_theorem(HEAD),
        forall_where(
            HEAD,
            is_value(var(HEAD)),
            computes_to(init_call(singleton(var(HEAD))), nil()),
        )
    );
    assert_eq!(
        init_cons_theorem(HEAD, NEXT, TAIL),
        forall_where(
            HEAD,
            is_value(var(HEAD)),
            forall_where(
                NEXT,
                is_value(var(NEXT)),
                forall_where(
                    TAIL,
                    is_list(var(TAIL)),
                    computes_to(
                        init_call(cons(var(HEAD), cons(var(NEXT), var(TAIL)))),
                        cons(var(HEAD), init_call(cons(var(NEXT), var(TAIL)))),
                    ),
                ),
            ),
        )
    );
}

#[test]
fn init_source_theorems_have_expected_shape() {
    let singleton_head = theorem_symbol("init_singleton", "head");
    let cons_head = theorem_symbol("init_cons", "head");
    let cons_next = theorem_symbol("init_cons", "next");
    let cons_tail = theorem_symbol("init_cons", "tail");

    assert_eq!(init_nil_errors_source_theorem(), init_nil_errors_theorem());
    assert_eq!(
        init_singleton_source_theorem(),
        init_singleton_theorem(singleton_head)
    );
    assert_eq!(
        init_cons_source_theorem(),
        init_cons_theorem(cons_head, cons_next, cons_tail)
    );
}

#[test]
fn null_theorems_have_expected_shape() {
    assert_eq!(
        null_nil_theorem(),
        computes_to(null_call(nil()), true_value())
    );
    assert_eq!(
        null_cons_theorem(HEAD, TAIL),
        forall_where(
            HEAD,
            is_value(var(HEAD)),
            forall_where(
                TAIL,
                is_list(var(TAIL)),
                computes_to(null_call(cons(var(HEAD), var(TAIL))), false_value()),
            ),
        )
    );
}

#[test]
fn null_source_theorems_have_expected_shape() {
    let cons_head = theorem_symbol("null_cons", "head");
    let cons_tail = theorem_symbol("null_cons", "tail");

    assert_eq!(null_nil_source_theorem(), null_nil_theorem());
    assert_eq!(
        null_cons_source_theorem(),
        null_cons_theorem(cons_head, cons_tail)
    );
}

#[test]
fn is_singleton_theorems_have_expected_shape() {
    assert_eq!(
        is_singleton_nil_theorem(),
        computes_to(is_singleton_call(nil()), false_value())
    );
    assert_eq!(
        is_singleton_singleton_theorem(HEAD),
        forall_where(
            HEAD,
            is_value(var(HEAD)),
            computes_to(is_singleton_call(singleton(var(HEAD))), true_value()),
        )
    );
    assert_eq!(
        is_singleton_cons_theorem(HEAD, NEXT, TAIL),
        forall_where(
            HEAD,
            is_value(var(HEAD)),
            forall_where(
                NEXT,
                is_value(var(NEXT)),
                forall_where(
                    TAIL,
                    is_list(var(TAIL)),
                    computes_to(
                        is_singleton_call(cons(var(HEAD), cons(var(NEXT), var(TAIL)))),
                        false_value(),
                    ),
                ),
            ),
        )
    );
}

#[test]
fn is_singleton_source_theorems_have_expected_shape() {
    let singleton_head = theorem_symbol("is_singleton_singleton", "head");
    let cons_head = theorem_symbol("is_singleton_cons", "head");
    let cons_next = theorem_symbol("is_singleton_cons", "next");
    let cons_tail = theorem_symbol("is_singleton_cons", "tail");

    assert_eq!(
        is_singleton_nil_source_theorem(),
        is_singleton_nil_theorem()
    );
    assert_eq!(
        is_singleton_singleton_source_theorem(),
        is_singleton_singleton_theorem(singleton_head)
    );
    assert_eq!(
        is_singleton_cons_source_theorem(),
        is_singleton_cons_theorem(cons_head, cons_next, cons_tail)
    );
}

#[test]
fn append_nil_computes_to_list_theorem_has_expected_shape() {
    assert_eq!(
        append_nil_computes_to_list_theorem(X, RESULT),
        forall_where(
            X,
            is_list(var(X)),
            exists_where(
                RESULT,
                is_list(var(RESULT)),
                computes_to(append_call(nil(), var(X)), var(RESULT)),
            ),
        )
    );
}

#[test]
fn append_nil_source_theorem_has_expected_shape() {
    let right = theorem_symbol("append_nil_computes_to_list", "right");
    let result = theorem_symbol("append_nil_computes_to_list", "result");

    assert_eq!(
        append_nil_computes_to_list_source_theorem(),
        append_nil_computes_to_list_theorem(right, result)
    );
}

#[test]
fn append_computes_to_list_theorem_has_expected_shape() {
    let appended = append_call(var(X), var(ACCUMULATOR));
    let right_case = exists_where(
        RESULT,
        is_list(var(RESULT)),
        computes_to(appended, var(RESULT)),
    );
    let left_case = forall_where(ACCUMULATOR, is_list(var(ACCUMULATOR)), right_case);

    assert_eq!(
        append_computes_to_list_theorem(X, ACCUMULATOR, RESULT),
        forall_where(X, is_list(var(X)), left_case)
    );
}

#[test]
fn append_source_theorem_has_expected_shape() {
    let left = theorem_symbol("append_computes_to_list", "left");
    let right = theorem_symbol("append_computes_to_list", "right");
    let result = theorem_symbol("append_computes_to_list", "result");

    assert_eq!(
        append_computes_to_list_source_theorem(),
        append_computes_to_list_theorem(left, right, result)
    );
}

#[test]
fn append_nil_returns_right_source_theorem_has_expected_shape() {
    let right = theorem_symbol("append_nil_returns_right", "right");

    assert_eq!(
        append_nil_returns_right_source_theorem(),
        append_nil_returns_right_theorem(right)
    );
}

#[test]
fn append_right_nil_source_theorem_has_expected_shape() {
    let left = theorem_symbol("append_right_nil", "left");

    assert_eq!(
        append_right_nil_source_theorem(),
        append_right_nil_theorem(left)
    );
}

#[test]
fn append_cons_theorem_has_expected_shape() {
    assert_eq!(
        append_cons_theorem(HEAD, TAIL, RIGHT_LIST),
        forall_where(
            HEAD,
            is_value(var(HEAD)),
            forall_where(
                TAIL,
                is_list(var(TAIL)),
                forall_where(
                    RIGHT_LIST,
                    is_list(var(RIGHT_LIST)),
                    computes_to(
                        append_call(cons(var(HEAD), var(TAIL)), var(RIGHT_LIST)),
                        cons(var(HEAD), append_call(var(TAIL), var(RIGHT_LIST))),
                    ),
                ),
            ),
        )
    );
}

#[test]
fn append_cons_source_theorem_has_expected_shape() {
    let head = theorem_symbol("append_cons", "head");
    let tail = theorem_symbol("append_cons", "tail");
    let right = theorem_symbol("append_cons", "right");

    assert_eq!(
        append_cons_source_theorem(),
        append_cons_theorem(head, tail, right)
    );
}

#[test]
fn append_singleton_theorem_has_expected_shape() {
    assert_eq!(
        append_singleton_theorem(HEAD, RIGHT_LIST),
        forall_where(
            HEAD,
            is_value(var(HEAD)),
            forall_where(
                RIGHT_LIST,
                is_list(var(RIGHT_LIST)),
                computes_to(
                    append_call(singleton(var(HEAD)), var(RIGHT_LIST)),
                    cons(var(HEAD), var(RIGHT_LIST)),
                ),
            ),
        )
    );
}

#[test]
fn append_singleton_source_theorem_has_expected_shape() {
    let head = theorem_symbol("append_singleton", "head");
    let right = theorem_symbol("append_singleton", "right");

    assert_eq!(
        append_singleton_source_theorem(),
        append_singleton_theorem(head, right)
    );
}

#[test]
fn append_assoc_theorem_has_expected_shape() {
    assert_eq!(
        append_assoc_theorem(X, ACCUMULATOR, RIGHT_LIST),
        forall_where(
            X,
            is_list(var(X)),
            forall_where(
                ACCUMULATOR,
                is_list(var(ACCUMULATOR)),
                forall_where(
                    RIGHT_LIST,
                    is_list(var(RIGHT_LIST)),
                    computes_to(
                        append_call(append_call(var(X), var(ACCUMULATOR)), var(RIGHT_LIST)),
                        append_call(var(X), append_call(var(ACCUMULATOR), var(RIGHT_LIST))),
                    ),
                ),
            ),
        )
    );
}

#[test]
fn append_assoc_source_theorem_has_expected_shape() {
    let left = theorem_symbol("append_assoc", "left");
    let middle = theorem_symbol("append_assoc", "middle");
    let right = theorem_symbol("append_assoc", "right");

    assert_eq!(
        append_assoc_source_theorem(),
        append_assoc_theorem(left, middle, right)
    );
}

#[test]
fn append_take_drop_theorem_has_expected_shape() {
    assert_eq!(
        append_take_drop_theorem(COUNT, X),
        forall_where(
            COUNT,
            is_list(var(COUNT)),
            forall_where(
                X,
                is_list(var(X)),
                computes_to(
                    append_call(take_call(var(COUNT), var(X)), drop_call(var(COUNT), var(X))),
                    var(X),
                ),
            ),
        )
    );
}

#[test]
fn append_take_drop_source_theorem_has_expected_shape() {
    let count = theorem_symbol("append_take_drop", "count");
    let list = theorem_symbol("append_take_drop", "list");

    assert_eq!(
        append_take_drop_source_theorem(),
        append_take_drop_theorem(count, list)
    );
}
