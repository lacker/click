use super::*;

#[test]
fn reverse_acc_computes_to_list_theorem_has_expected_shape() {
    assert_eq!(
        reverse_acc_computes_to_list_theorem(X, ACCUMULATOR, RESULT),
        forall_where(
            X,
            is_list(var(X)),
            forall_where(
                ACCUMULATOR,
                is_list(var(ACCUMULATOR)),
                exists_where(
                    RESULT,
                    is_list(var(RESULT)),
                    computes_to(reverse_acc_call(var(X), var(ACCUMULATOR)), var(RESULT)),
                ),
            ),
        )
    );
}

#[test]
fn reverse_acc_source_theorem_has_expected_shape() {
    let list = theorem_symbol("reverse_acc_computes_to_list", "list");
    let acc = theorem_symbol("reverse_acc_computes_to_list", "acc");
    let result = theorem_symbol("reverse_acc_computes_to_list", "result");

    assert_eq!(
        reverse_acc_computes_to_list_source_theorem(),
        reverse_acc_computes_to_list_theorem(list, acc, result)
    );
}

#[test]
fn reverse_computes_to_list_theorem_has_expected_shape() {
    assert_eq!(
        reverse_computes_to_list_theorem(X, RESULT),
        forall_where(
            X,
            is_list(var(X)),
            exists_where(
                RESULT,
                is_list(var(RESULT)),
                computes_to(reverse_call(var(X)), var(RESULT)),
            ),
        )
    );
}

#[test]
fn reverse_source_theorem_has_expected_shape() {
    let list = theorem_symbol("reverse_computes_to_list", "list");
    let result = theorem_symbol("reverse_computes_to_list", "result");

    assert_eq!(
        reverse_computes_to_list_source_theorem(),
        reverse_computes_to_list_theorem(list, result)
    );
}

#[test]
fn reverse_nil_source_theorem_has_expected_shape() {
    let result = theorem_symbol("reverse_nil_computes_to_list", "result");

    assert_eq!(
        reverse_nil_computes_to_list_source_theorem(),
        computes_to_list(result, reverse_call(nil()))
    );
}

#[test]
fn reverse_nil_exact_source_theorem_has_expected_shape() {
    assert_eq!(reverse_nil_source_theorem(), reverse_nil_theorem());
}

#[test]
fn reverse_singleton_theorem_has_expected_shape() {
    assert_eq!(
        reverse_singleton_theorem(HEAD),
        forall_where(
            HEAD,
            is_value(var(HEAD)),
            computes_to(reverse_call(singleton(var(HEAD))), singleton(var(HEAD))),
        )
    );
}

#[test]
fn reverse_singleton_source_theorem_has_expected_shape() {
    let head = theorem_symbol("reverse_singleton", "head");

    assert_eq!(
        reverse_singleton_source_theorem(),
        reverse_singleton_theorem(head)
    );
}

#[test]
fn reverse_acc_append_theorem_has_expected_shape() {
    assert_eq!(
        reverse_acc_append_theorem(X, ACCUMULATOR),
        forall_where(
            X,
            is_list(var(X)),
            forall_where(
                ACCUMULATOR,
                is_list(var(ACCUMULATOR)),
                computes_to(
                    reverse_acc_call(var(X), var(ACCUMULATOR)),
                    append_call(reverse_call(var(X)), var(ACCUMULATOR)),
                ),
            ),
        )
    );
}

#[test]
fn reverse_acc_append_source_theorem_has_expected_shape() {
    let list = theorem_symbol("reverse_acc_append", "list");
    let acc = theorem_symbol("reverse_acc_append", "acc");

    assert_eq!(
        reverse_acc_append_source_theorem(),
        reverse_acc_append_theorem(list, acc)
    );
}

#[test]
fn reverse_cons_theorem_has_expected_shape() {
    assert_eq!(
        reverse_cons_theorem(HEAD, TAIL),
        forall_where(
            HEAD,
            is_value(var(HEAD)),
            forall_where(
                TAIL,
                is_list(var(TAIL)),
                computes_to(
                    reverse_call(cons(var(HEAD), var(TAIL))),
                    append_call(reverse_call(var(TAIL)), singleton(var(HEAD))),
                ),
            ),
        )
    );
}

#[test]
fn reverse_cons_source_theorem_has_expected_shape() {
    let head = theorem_symbol("reverse_cons", "head");
    let tail = theorem_symbol("reverse_cons", "tail");

    assert_eq!(
        reverse_cons_source_theorem(),
        reverse_cons_theorem(head, tail)
    );
}

#[test]
fn reverse_acc_reverse_theorem_has_expected_shape() {
    assert_eq!(
        reverse_acc_reverse_theorem(X, ACCUMULATOR),
        forall_where(
            X,
            is_list(var(X)),
            forall_where(
                ACCUMULATOR,
                is_list(var(ACCUMULATOR)),
                computes_to(
                    reverse_call(reverse_acc_call(var(X), var(ACCUMULATOR))),
                    append_call(reverse_call(var(ACCUMULATOR)), var(X)),
                ),
            ),
        )
    );
}

#[test]
fn reverse_acc_reverse_source_theorem_has_expected_shape() {
    let list = theorem_symbol("reverse_acc_reverse", "list");
    let acc = theorem_symbol("reverse_acc_reverse", "acc");

    assert_eq!(
        reverse_acc_reverse_source_theorem(),
        reverse_acc_reverse_theorem(list, acc)
    );
}

#[test]
fn reverse_double_theorem_has_expected_shape() {
    assert_eq!(
        reverse_double_theorem(X),
        forall_where(
            X,
            is_list(var(X)),
            computes_to(reverse_call(reverse_call(var(X))), var(X)),
        )
    );
}

#[test]
fn reverse_double_source_theorem_has_expected_shape() {
    let list = theorem_symbol("reverse_double", "list");

    assert_eq!(
        reverse_double_source_theorem(),
        reverse_double_theorem(list)
    );
}

#[test]
fn reverse_acc_of_append_theorem_has_expected_shape() {
    assert_eq!(
        reverse_acc_of_append_theorem(X, RIGHT_LIST, ACCUMULATOR),
        forall_where(
            X,
            is_list(var(X)),
            forall_where(
                RIGHT_LIST,
                is_list(var(RIGHT_LIST)),
                forall_where(
                    ACCUMULATOR,
                    is_list(var(ACCUMULATOR)),
                    computes_to(
                        reverse_acc_call(append_call(var(X), var(RIGHT_LIST)), var(ACCUMULATOR),),
                        reverse_acc_call(
                            var(RIGHT_LIST),
                            reverse_acc_call(var(X), var(ACCUMULATOR)),
                        ),
                    ),
                ),
            ),
        )
    );
}

#[test]
fn reverse_acc_of_append_source_theorem_has_expected_shape() {
    let left = theorem_symbol("reverse_acc_of_append", "left");
    let right = theorem_symbol("reverse_acc_of_append", "right");
    let acc = theorem_symbol("reverse_acc_of_append", "acc");

    assert_eq!(
        reverse_acc_of_append_source_theorem(),
        reverse_acc_of_append_theorem(left, right, acc)
    );
}

#[test]
fn reverse_append_theorem_has_expected_shape() {
    assert_eq!(
        reverse_append_theorem(X, RIGHT_LIST),
        forall_where(
            X,
            is_list(var(X)),
            forall_where(
                RIGHT_LIST,
                is_list(var(RIGHT_LIST)),
                computes_to(
                    reverse_call(append_call(var(X), var(RIGHT_LIST))),
                    append_call(reverse_call(var(RIGHT_LIST)), reverse_call(var(X))),
                ),
            ),
        )
    );
}

#[test]
fn reverse_append_source_theorem_has_expected_shape() {
    let left = theorem_symbol("reverse_append", "left");
    let right = theorem_symbol("reverse_append", "right");

    assert_eq!(
        reverse_append_source_theorem(),
        reverse_append_theorem(left, right)
    );
}

#[test]
fn snoc_computes_to_list_theorem_has_expected_shape() {
    assert_eq!(
        snoc_computes_to_list_theorem(X, HEAD, RESULT),
        forall_where(
            X,
            is_list(var(X)),
            forall_where(
                HEAD,
                is_value(var(HEAD)),
                exists_where(
                    RESULT,
                    is_list(var(RESULT)),
                    computes_to(snoc_call(var(X), var(HEAD)), var(RESULT)),
                ),
            ),
        )
    );
}

#[test]
fn snoc_source_theorem_has_expected_shape() {
    let list = theorem_symbol("snoc_computes_to_list", "list");
    let value = theorem_symbol("snoc_computes_to_list", "value");
    let result = theorem_symbol("snoc_computes_to_list", "result");

    assert_eq!(
        snoc_computes_to_list_source_theorem(),
        snoc_computes_to_list_theorem(list, value, result)
    );
}

#[test]
fn snoc_exact_theorems_have_expected_shape() {
    assert_eq!(snoc_nil_theorem(HEAD), {
        forall_where(
            HEAD,
            is_value(var(HEAD)),
            computes_to(snoc_call(nil(), var(HEAD)), singleton(var(HEAD))),
        )
    });
    assert_eq!(
        snoc_cons_theorem(HEAD, TAIL, NEXT),
        forall_where(
            HEAD,
            is_value(var(HEAD)),
            forall_where(
                TAIL,
                is_list(var(TAIL)),
                forall_where(
                    NEXT,
                    is_value(var(NEXT)),
                    computes_to(
                        snoc_call(cons(var(HEAD), var(TAIL)), var(NEXT)),
                        cons(var(HEAD), snoc_call(var(TAIL), var(NEXT))),
                    ),
                ),
            ),
        )
    );
}

#[test]
fn snoc_exact_source_theorems_have_expected_shape() {
    let nil_value = theorem_symbol("snoc_nil", "value");
    let cons_head = theorem_symbol("snoc_cons", "head");
    let cons_tail = theorem_symbol("snoc_cons", "tail");
    let cons_value = theorem_symbol("snoc_cons", "value");

    assert_eq!(snoc_nil_source_theorem(), snoc_nil_theorem(nil_value));
    assert_eq!(
        snoc_cons_source_theorem(),
        snoc_cons_theorem(cons_head, cons_tail, cons_value)
    );
}

#[test]
fn concat_nil_source_theorem_has_expected_shape() {
    assert_eq!(concat_nil_source_theorem(), concat_nil_theorem());
}

#[test]
fn length_theorems_have_expected_shape() {
    assert_eq!(length_nil_theorem(), computes_to(length_call(nil()), nil()));
    assert_eq!(
        length_cons_theorem(HEAD, TAIL),
        forall_where(
            HEAD,
            is_value(var(HEAD)),
            forall_where(
                TAIL,
                is_list(var(TAIL)),
                computes_to(
                    length_call(cons(var(HEAD), var(TAIL))),
                    cons(unit(), length_call(var(TAIL))),
                ),
            ),
        )
    );
    assert_eq!(
        length_singleton_theorem(HEAD),
        forall_where(
            HEAD,
            is_value(var(HEAD)),
            computes_to(length_call(singleton(var(HEAD))), singleton(unit())),
        )
    );
    assert_eq!(
        length_computes_to_list_theorem(X, RESULT),
        forall_where(
            X,
            is_list(var(X)),
            computes_to_list(RESULT, length_call(var(X))),
        )
    );
    assert_eq!(
        length_append_theorem(X, RIGHT_LIST),
        forall_where(
            X,
            is_list(var(X)),
            forall_where(
                RIGHT_LIST,
                is_list(var(RIGHT_LIST)),
                computes_to(
                    length_call(append_call(var(X), var(RIGHT_LIST))),
                    append_call(length_call(var(X)), length_call(var(RIGHT_LIST))),
                ),
            ),
        )
    );
    assert_eq!(
        length_map_theorem(FUNCTION, VALUE, MAPPED_VALUE, X),
        forall_where(
            FUNCTION,
            is_value(var(FUNCTION)),
            implies(
                forall_where(
                    VALUE,
                    is_value(var(VALUE)),
                    exists_where(
                        MAPPED_VALUE,
                        is_value(var(MAPPED_VALUE)),
                        computes_to(apply(var(FUNCTION), var(VALUE)), var(MAPPED_VALUE)),
                    ),
                ),
                forall_where(
                    X,
                    is_list(var(X)),
                    computes_to(
                        length_call(map_call(var(FUNCTION), var(X))),
                        length_call(var(X)),
                    ),
                ),
            ),
        )
    );
}

#[test]
fn length_source_theorems_have_expected_shape() {
    let cons_head = theorem_symbol("length_cons", "head");
    let cons_tail = theorem_symbol("length_cons", "tail");
    let singleton_head = theorem_symbol("length_singleton", "head");
    let computes_list = theorem_symbol("length_computes_to_list", "list");
    let computes_result = theorem_symbol("length_computes_to_list", "result");
    let append_left = theorem_symbol("length_append", "left");
    let append_right = theorem_symbol("length_append", "right");

    assert_eq!(length_nil_source_theorem(), length_nil_theorem());
    assert_eq!(
        length_cons_source_theorem(),
        length_cons_theorem(cons_head, cons_tail)
    );
    assert_eq!(
        length_singleton_source_theorem(),
        length_singleton_theorem(singleton_head)
    );
    assert_eq!(
        length_computes_to_list_source_theorem(),
        length_computes_to_list_theorem(computes_list, computes_result)
    );
    assert_eq!(
        length_append_source_theorem(),
        length_append_theorem(append_left, append_right)
    );
}

#[test]
fn map_theorems_have_expected_shape() {
    assert_eq!(
        map_nil_theorem(FUNCTION),
        forall_where(
            FUNCTION,
            is_value(var(FUNCTION)),
            computes_to(map_call(var(FUNCTION), nil()), nil()),
        )
    );
    assert_eq!(
        map_cons_theorem(FUNCTION, HEAD, TAIL),
        forall_where(
            FUNCTION,
            is_value(var(FUNCTION)),
            forall_where(
                HEAD,
                is_value(var(HEAD)),
                forall_where(
                    TAIL,
                    is_list(var(TAIL)),
                    computes_to(
                        map_call(var(FUNCTION), cons(var(HEAD), var(TAIL))),
                        cons(
                            apply(var(FUNCTION), var(HEAD)),
                            map_call(var(FUNCTION), var(TAIL)),
                        ),
                    ),
                ),
            ),
        )
    );
    assert_eq!(
        map_computes_to_list_theorem(FUNCTION, VALUE, MAPPED_VALUE, X, RESULT),
        forall_where(
            FUNCTION,
            is_value(var(FUNCTION)),
            implies(
                forall_where(
                    VALUE,
                    is_value(var(VALUE)),
                    exists_where(
                        MAPPED_VALUE,
                        is_value(var(MAPPED_VALUE)),
                        computes_to(apply(var(FUNCTION), var(VALUE)), var(MAPPED_VALUE),),
                    ),
                ),
                forall_where(
                    X,
                    is_list(var(X)),
                    computes_to_list(RESULT, map_call(var(FUNCTION), var(X))),
                ),
            ),
        )
    );
}

#[test]
fn map_source_theorems_have_expected_shape() {
    let nil_function = theorem_symbol("map_nil", "function");
    let cons_function = theorem_symbol("map_cons", "function");
    let cons_head = theorem_symbol("map_cons", "head");
    let cons_tail = theorem_symbol("map_cons", "tail");
    let computes_function = theorem_symbol("map_computes_to_list", "function");
    let computes_value = theorem_symbol("map_computes_to_list", "value");
    let computes_mapped_value = theorem_symbol("map_computes_to_list", "mapped_value");
    let computes_list = theorem_symbol("map_computes_to_list", "list");
    let computes_result = theorem_symbol("map_computes_to_list", "result");

    assert_eq!(map_nil_source_theorem(), map_nil_theorem(nil_function));
    assert_eq!(
        map_cons_source_theorem(),
        map_cons_theorem(cons_function, cons_head, cons_tail)
    );
    assert_eq!(
        map_computes_to_list_source_theorem(),
        map_computes_to_list_theorem(
            computes_function,
            computes_value,
            computes_mapped_value,
            computes_list,
            computes_result,
        )
    );
}

#[test]
fn length_map_source_theorem_has_expected_shape() {
    let function = theorem_symbol("length_map", "function");
    let value = theorem_symbol("length_map", "value");
    let mapped_value = theorem_symbol("length_map", "mapped_value");
    let list = theorem_symbol("length_map", "list");

    assert_eq!(
        length_map_source_theorem(),
        length_map_theorem(function, value, mapped_value, list)
    );
}

#[test]
fn take_theorems_have_expected_shape() {
    assert_eq!(
        take_zero_theorem(X),
        forall_where(
            X,
            is_list(var(X)),
            computes_to(take_call(nil(), var(X)), nil()),
        )
    );
    assert_eq!(
        take_nil_theorem(COUNT),
        forall_where(
            COUNT,
            is_list(var(COUNT)),
            computes_to(take_call(var(COUNT), nil()), nil()),
        )
    );
    assert_eq!(
        take_cons_theorem(COUNT_HEAD, COUNT_TAIL, HEAD, TAIL),
        forall_where(
            COUNT_HEAD,
            is_value(var(COUNT_HEAD)),
            forall_where(
                COUNT_TAIL,
                is_list(var(COUNT_TAIL)),
                forall_where(
                    HEAD,
                    is_value(var(HEAD)),
                    forall_where(
                        TAIL,
                        is_list(var(TAIL)),
                        computes_to(
                            take_call(
                                cons(var(COUNT_HEAD), var(COUNT_TAIL)),
                                cons(var(HEAD), var(TAIL)),
                            ),
                            cons(var(HEAD), take_call(var(COUNT_TAIL), var(TAIL))),
                        ),
                    ),
                ),
            ),
        )
    );
    assert_eq!(
        take_computes_to_list_theorem(COUNT, X, RESULT),
        forall_where(
            COUNT,
            is_list(var(COUNT)),
            forall_where(
                X,
                is_list(var(X)),
                computes_to_list(RESULT, take_call(var(COUNT), var(X))),
            ),
        )
    );
}

#[test]
fn take_source_theorems_have_expected_shape() {
    let zero_list = theorem_symbol("take_zero", "list");
    let nil_count = theorem_symbol("take_nil", "count");
    let cons_count_head = theorem_symbol("take_cons", "count_head");
    let cons_count_tail = theorem_symbol("take_cons", "count_tail");
    let cons_head = theorem_symbol("take_cons", "head");
    let cons_tail = theorem_symbol("take_cons", "tail");
    let computes_count = theorem_symbol("take_computes_to_list", "count");
    let computes_list = theorem_symbol("take_computes_to_list", "list");
    let computes_result = theorem_symbol("take_computes_to_list", "result");

    assert_eq!(take_zero_source_theorem(), take_zero_theorem(zero_list));
    assert_eq!(take_nil_source_theorem(), take_nil_theorem(nil_count));
    assert_eq!(
        take_cons_source_theorem(),
        take_cons_theorem(cons_count_head, cons_count_tail, cons_head, cons_tail)
    );
    assert_eq!(
        take_computes_to_list_source_theorem(),
        take_computes_to_list_theorem(computes_count, computes_list, computes_result)
    );
}

#[test]
fn drop_theorems_have_expected_shape() {
    assert_eq!(
        drop_zero_theorem(X),
        forall_where(
            X,
            is_list(var(X)),
            computes_to(drop_call(nil(), var(X)), var(X)),
        )
    );
    assert_eq!(
        drop_nil_theorem(COUNT),
        forall_where(
            COUNT,
            is_list(var(COUNT)),
            computes_to(drop_call(var(COUNT), nil()), nil()),
        )
    );
    assert_eq!(
        drop_cons_theorem(COUNT_HEAD, COUNT_TAIL, HEAD, TAIL),
        forall_where(
            COUNT_HEAD,
            is_value(var(COUNT_HEAD)),
            forall_where(
                COUNT_TAIL,
                is_list(var(COUNT_TAIL)),
                forall_where(
                    HEAD,
                    is_value(var(HEAD)),
                    forall_where(
                        TAIL,
                        is_list(var(TAIL)),
                        computes_to(
                            drop_call(
                                cons(var(COUNT_HEAD), var(COUNT_TAIL)),
                                cons(var(HEAD), var(TAIL)),
                            ),
                            drop_call(var(COUNT_TAIL), var(TAIL)),
                        ),
                    ),
                ),
            ),
        )
    );
    assert_eq!(
        drop_computes_to_list_theorem(COUNT, X, RESULT),
        forall_where(
            COUNT,
            is_list(var(COUNT)),
            forall_where(
                X,
                is_list(var(X)),
                computes_to_list(RESULT, drop_call(var(COUNT), var(X))),
            ),
        )
    );
}

#[test]
fn drop_source_theorems_have_expected_shape() {
    let zero_list = theorem_symbol("drop_zero", "list");
    let nil_count = theorem_symbol("drop_nil", "count");
    let cons_count_head = theorem_symbol("drop_cons", "count_head");
    let cons_count_tail = theorem_symbol("drop_cons", "count_tail");
    let cons_head = theorem_symbol("drop_cons", "head");
    let cons_tail = theorem_symbol("drop_cons", "tail");
    let computes_count = theorem_symbol("drop_computes_to_list", "count");
    let computes_list = theorem_symbol("drop_computes_to_list", "list");
    let computes_result = theorem_symbol("drop_computes_to_list", "result");

    assert_eq!(drop_zero_source_theorem(), drop_zero_theorem(zero_list));
    assert_eq!(drop_nil_source_theorem(), drop_nil_theorem(nil_count));
    assert_eq!(
        drop_cons_source_theorem(),
        drop_cons_theorem(cons_count_head, cons_count_tail, cons_head, cons_tail)
    );
    assert_eq!(
        drop_computes_to_list_source_theorem(),
        drop_computes_to_list_theorem(computes_count, computes_list, computes_result)
    );
}

#[test]
fn split_at_source_theorems_have_expected_shape() {
    let def_count = theorem_symbol("split_at_def", "count");
    let def_list = theorem_symbol("split_at_def", "list");
    let zero_list = theorem_symbol("split_at_zero", "list");
    let nil_count = theorem_symbol("split_at_nil", "count");
    let cons_count_head = theorem_symbol("split_at_cons", "count_head");
    let cons_count_tail = theorem_symbol("split_at_cons", "count_tail");
    let cons_head = theorem_symbol("split_at_cons", "head");
    let cons_tail = theorem_symbol("split_at_cons", "tail");

    assert_eq!(
        split_at_def_source_theorem(),
        split_at_def_theorem(def_count, def_list)
    );
    assert_eq!(
        split_at_zero_source_theorem(),
        split_at_zero_theorem(zero_list)
    );
    assert_eq!(
        split_at_nil_source_theorem(),
        split_at_nil_theorem(nil_count)
    );
    assert_eq!(
        split_at_cons_source_theorem(),
        split_at_cons_theorem(cons_count_head, cons_count_tail, cons_head, cons_tail)
    );
}

#[test]
fn nth_theorems_have_expected_shape() {
    assert_eq!(
        nth_zero_nil_theorem(),
        computes_to(nth_call(nil(), nil()), none())
    );
    assert_eq!(
        nth_zero_cons_theorem(HEAD, TAIL),
        forall_where(
            HEAD,
            is_value(var(HEAD)),
            forall_where(
                TAIL,
                is_list(var(TAIL)),
                computes_to(
                    nth_call(nil(), cons(var(HEAD), var(TAIL))),
                    some_call(var(HEAD))
                ),
            ),
        )
    );
    assert_eq!(
        nth_cons_nil_theorem(COUNT_HEAD, COUNT_TAIL),
        forall_where(
            COUNT_HEAD,
            is_value(var(COUNT_HEAD)),
            forall_where(
                COUNT_TAIL,
                is_list(var(COUNT_TAIL)),
                computes_to(
                    nth_call(cons(var(COUNT_HEAD), var(COUNT_TAIL)), nil()),
                    none()
                ),
            ),
        )
    );
    assert_eq!(
        nth_cons_cons_theorem(COUNT_HEAD, COUNT_TAIL, HEAD, TAIL),
        forall_where(
            COUNT_HEAD,
            is_value(var(COUNT_HEAD)),
            forall_where(
                COUNT_TAIL,
                is_list(var(COUNT_TAIL)),
                forall_where(
                    HEAD,
                    is_value(var(HEAD)),
                    forall_where(
                        TAIL,
                        is_list(var(TAIL)),
                        computes_to(
                            nth_call(
                                cons(var(COUNT_HEAD), var(COUNT_TAIL)),
                                cons(var(HEAD), var(TAIL)),
                            ),
                            nth_call(var(COUNT_TAIL), var(TAIL)),
                        ),
                    ),
                ),
            ),
        )
    );
}

#[test]
fn nth_source_theorems_have_expected_shape() {
    let zero_cons_head = theorem_symbol("nth_zero_cons", "head");
    let zero_cons_tail = theorem_symbol("nth_zero_cons", "tail");
    let cons_nil_index_head = theorem_symbol("nth_cons_nil", "index_head");
    let cons_nil_index_tail = theorem_symbol("nth_cons_nil", "index_tail");
    let cons_cons_index_head = theorem_symbol("nth_cons_cons", "index_head");
    let cons_cons_index_tail = theorem_symbol("nth_cons_cons", "index_tail");
    let cons_cons_head = theorem_symbol("nth_cons_cons", "head");
    let cons_cons_tail = theorem_symbol("nth_cons_cons", "tail");

    assert_eq!(nth_zero_nil_source_theorem(), nth_zero_nil_theorem());
    assert_eq!(
        nth_zero_cons_source_theorem(),
        nth_zero_cons_theorem(zero_cons_head, zero_cons_tail)
    );
    assert_eq!(
        nth_cons_nil_source_theorem(),
        nth_cons_nil_theorem(cons_nil_index_head, cons_nil_index_tail)
    );
    assert_eq!(
        nth_cons_cons_source_theorem(),
        nth_cons_cons_theorem(
            cons_cons_index_head,
            cons_cons_index_tail,
            cons_cons_head,
            cons_cons_tail,
        )
    );
}

#[test]
fn replicate_theorems_have_expected_shape() {
    assert_eq!(
        replicate_zero_theorem(VALUE),
        forall_where(
            VALUE,
            is_value(var(VALUE)),
            computes_to(replicate_call(nil(), var(VALUE)), nil()),
        )
    );
    assert_eq!(
        replicate_cons_theorem(COUNT_HEAD, COUNT_TAIL, VALUE),
        forall_where(
            COUNT_HEAD,
            is_value(var(COUNT_HEAD)),
            forall_where(
                COUNT_TAIL,
                is_list(var(COUNT_TAIL)),
                forall_where(
                    VALUE,
                    is_value(var(VALUE)),
                    computes_to(
                        replicate_call(cons(var(COUNT_HEAD), var(COUNT_TAIL)), var(VALUE)),
                        cons(var(VALUE), replicate_call(var(COUNT_TAIL), var(VALUE))),
                    ),
                ),
            ),
        )
    );
    assert_eq!(
        replicate_computes_to_list_theorem(COUNT, VALUE, RESULT),
        forall_where(
            COUNT,
            is_list(var(COUNT)),
            forall_where(
                VALUE,
                is_value(var(VALUE)),
                computes_to_list(RESULT, replicate_call(var(COUNT), var(VALUE))),
            ),
        )
    );
    assert_eq!(
        length_replicate_theorem(COUNT, VALUE),
        forall_where(
            COUNT,
            is_list(var(COUNT)),
            forall_where(
                VALUE,
                is_value(var(VALUE)),
                computes_to(
                    length_call(replicate_call(var(COUNT), var(VALUE))),
                    length_call(var(COUNT)),
                ),
            ),
        )
    );
}

#[test]
fn replicate_source_theorems_have_expected_shape() {
    let zero_value = theorem_symbol("replicate_zero", "value");
    let cons_count_head = theorem_symbol("replicate_cons", "count_head");
    let cons_count_tail = theorem_symbol("replicate_cons", "count_tail");
    let cons_value = theorem_symbol("replicate_cons", "value");
    let computes_count = theorem_symbol("replicate_computes_to_list", "count");
    let computes_value = theorem_symbol("replicate_computes_to_list", "value");
    let computes_result = theorem_symbol("replicate_computes_to_list", "result");
    let length_count = theorem_symbol("length_replicate", "count");
    let length_value = theorem_symbol("length_replicate", "value");

    assert_eq!(
        replicate_zero_source_theorem(),
        replicate_zero_theorem(zero_value)
    );
    assert_eq!(
        replicate_cons_source_theorem(),
        replicate_cons_theorem(cons_count_head, cons_count_tail, cons_value)
    );
    assert_eq!(
        replicate_computes_to_list_source_theorem(),
        replicate_computes_to_list_theorem(computes_count, computes_value, computes_result)
    );
    assert_eq!(
        length_replicate_source_theorem(),
        length_replicate_theorem(length_count, length_value)
    );
}

#[test]
fn intersperse_theorems_have_expected_shape() {
    assert_eq!(
        intersperse_nil_theorem(VALUE),
        forall_where(
            VALUE,
            is_value(var(VALUE)),
            computes_to(intersperse_call(var(VALUE), nil()), nil()),
        )
    );
    assert_eq!(
        intersperse_singleton_theorem(VALUE, HEAD),
        forall_where(
            VALUE,
            is_value(var(VALUE)),
            forall_where(
                HEAD,
                is_value(var(HEAD)),
                computes_to(
                    intersperse_call(var(VALUE), singleton(var(HEAD))),
                    singleton(var(HEAD)),
                ),
            ),
        )
    );
    assert_eq!(
        intersperse_cons_cons_theorem(VALUE, HEAD, NEXT, TAIL),
        forall_where(
            VALUE,
            is_value(var(VALUE)),
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
                            intersperse_call(
                                var(VALUE),
                                cons(var(HEAD), cons(var(NEXT), var(TAIL))),
                            ),
                            cons(
                                var(HEAD),
                                cons(
                                    var(VALUE),
                                    intersperse_call(var(VALUE), cons(var(NEXT), var(TAIL)),),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
    );
    assert_eq!(
        intersperse_cons_computes_to_list_theorem(VALUE, TAIL, HEAD, RESULT),
        forall_where(
            VALUE,
            is_value(var(VALUE)),
            forall_where(
                TAIL,
                is_list(var(TAIL)),
                forall_where(
                    HEAD,
                    is_value(var(HEAD)),
                    computes_to_list(
                        RESULT,
                        intersperse_call(var(VALUE), cons(var(HEAD), var(TAIL))),
                    ),
                ),
            ),
        )
    );
    assert_eq!(
        intersperse_computes_to_list_theorem(VALUE, X, RESULT),
        forall_where(
            VALUE,
            is_value(var(VALUE)),
            forall_where(
                X,
                is_list(var(X)),
                computes_to_list(RESULT, intersperse_call(var(VALUE), var(X))),
            ),
        )
    );
}

#[test]
fn intersperse_source_theorems_have_expected_shape() {
    let nil_separator = theorem_symbol("intersperse_nil", "separator");
    let singleton_separator = theorem_symbol("intersperse_singleton", "separator");
    let singleton_head = theorem_symbol("intersperse_singleton", "head");
    let cons_separator = theorem_symbol("intersperse_cons_cons", "separator");
    let cons_head = theorem_symbol("intersperse_cons_cons", "head");
    let cons_next = theorem_symbol("intersperse_cons_cons", "next");
    let cons_tail = theorem_symbol("intersperse_cons_cons", "tail");
    let cons_computes_separator = theorem_symbol("intersperse_cons_computes_to_list", "separator");
    let cons_computes_tail = theorem_symbol("intersperse_cons_computes_to_list", "tail");
    let cons_computes_head = theorem_symbol("intersperse_cons_computes_to_list", "head");
    let cons_computes_result = theorem_symbol("intersperse_cons_computes_to_list", "result");
    let computes_separator = theorem_symbol("intersperse_computes_to_list", "separator");
    let computes_list = theorem_symbol("intersperse_computes_to_list", "list");
    let computes_result = theorem_symbol("intersperse_computes_to_list", "result");

    assert_eq!(
        intersperse_nil_source_theorem(),
        intersperse_nil_theorem(nil_separator)
    );
    assert_eq!(
        intersperse_singleton_source_theorem(),
        intersperse_singleton_theorem(singleton_separator, singleton_head)
    );
    assert_eq!(
        intersperse_cons_cons_source_theorem(),
        intersperse_cons_cons_theorem(cons_separator, cons_head, cons_next, cons_tail)
    );
    assert_eq!(
        intersperse_cons_computes_to_list_source_theorem(),
        intersperse_cons_computes_to_list_theorem(
            cons_computes_separator,
            cons_computes_tail,
            cons_computes_head,
            cons_computes_result
        )
    );
    assert_eq!(
        intersperse_computes_to_list_source_theorem(),
        intersperse_computes_to_list_theorem(computes_separator, computes_list, computes_result)
    );
}

#[test]
fn intercalate_theorems_have_expected_shape() {
    assert_eq!(
        intercalate_nil_theorem(VALUE),
        forall_where(
            VALUE,
            is_list(var(VALUE)),
            computes_to(intercalate_call(var(VALUE), nil()), nil()),
        )
    );
    assert_eq!(
        intercalate_singleton_theorem(VALUE, X),
        forall_where(
            VALUE,
            is_list(var(VALUE)),
            forall_where(
                X,
                is_list(var(X)),
                computes_to(intercalate_call(var(VALUE), singleton(var(X))), var(X),),
            ),
        )
    );
    assert_eq!(
        intercalate_cons_cons_theorem(VALUE, HEAD, NEXT, TAIL),
        forall_where(
            VALUE,
            is_list(var(VALUE)),
            forall_where(
                HEAD,
                is_list(var(HEAD)),
                forall_where(
                    NEXT,
                    is_list(var(NEXT)),
                    forall_where(
                        TAIL,
                        is_list(var(TAIL)),
                        computes_to(
                            intercalate_call(
                                var(VALUE),
                                cons(var(HEAD), cons(var(NEXT), var(TAIL))),
                            ),
                            append_call(
                                var(HEAD),
                                append_call(
                                    var(VALUE),
                                    intercalate_call(var(VALUE), cons(var(NEXT), var(TAIL)),),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
    );
    assert_eq!(
        is_list_value_true_implies_is_list_theorem(VALUE),
        forall_where(
            VALUE,
            is_value(var(VALUE)),
            implies(
                computes_to(is_list_value_call(var(VALUE)), true_value()),
                is_list(var(VALUE)),
            ),
        )
    );
    assert_eq!(
        all_lists_cons_true_theorem(HEAD, TAIL),
        forall_where(
            HEAD,
            is_value(var(HEAD)),
            forall_where(
                TAIL,
                is_list(var(TAIL)),
                implies(
                    computes_to(all_lists_call(cons(var(HEAD), var(TAIL))), true_value()),
                    and(
                        is_list(var(HEAD)),
                        computes_to(all_lists_call(var(TAIL)), true_value()),
                    ),
                ),
            ),
        )
    );
    assert_eq!(
        none_is_none_theorem(),
        computes_to(is_none_call(none()), true_value())
    );
    assert_eq!(
        some_is_none_theorem(VALUE),
        forall_where(
            VALUE,
            is_value(var(VALUE)),
            computes_to(is_none_call(some_call(var(VALUE))), false_value()),
        )
    );
    assert_eq!(
        none_is_some_theorem(),
        computes_to(is_some_call(none()), false_value())
    );
    assert_eq!(
        some_is_some_theorem(VALUE),
        forall_where(
            VALUE,
            is_value(var(VALUE)),
            computes_to(is_some_call(some_call(var(VALUE))), true_value()),
        )
    );
    assert_eq!(
        intercalate_cons_computes_to_list_theorem(VALUE, TAIL, HEAD, RESULT),
        forall_where(
            VALUE,
            is_list(var(VALUE)),
            forall_where(
                TAIL,
                is_list(var(TAIL)),
                forall_where(
                    HEAD,
                    is_value(var(HEAD)),
                    implies(
                        computes_to(all_lists_call(cons(var(HEAD), var(TAIL))), true_value()),
                        computes_to_list(
                            RESULT,
                            intercalate_call(var(VALUE), cons(var(HEAD), var(TAIL))),
                        ),
                    ),
                ),
            ),
        )
    );
    assert_eq!(
        intercalate_computes_to_list_theorem(VALUE, X, RESULT),
        forall_where(
            VALUE,
            is_list(var(VALUE)),
            forall_where(
                X,
                is_list(var(X)),
                implies(
                    computes_to(all_lists_call(var(X)), true_value()),
                    computes_to_list(RESULT, intercalate_call(var(VALUE), var(X))),
                ),
            ),
        )
    );
}

#[test]
fn intercalate_source_theorems_have_expected_shape() {
    let nil_separator = theorem_symbol("intercalate_nil", "separator");
    let singleton_separator = theorem_symbol("intercalate_singleton", "separator");
    let singleton_list = theorem_symbol("intercalate_singleton", "list");
    let cons_separator = theorem_symbol("intercalate_cons_cons", "separator");
    let cons_head = theorem_symbol("intercalate_cons_cons", "head");
    let cons_next = theorem_symbol("intercalate_cons_cons", "next");
    let cons_tail = theorem_symbol("intercalate_cons_cons", "tail");
    let list_value = theorem_symbol("is_list_value_true_implies_is_list", "value");
    let all_lists_head = theorem_symbol("all_lists_cons_true", "head");
    let all_lists_tail = theorem_symbol("all_lists_cons_true", "tail");
    let some_is_none_value = theorem_symbol("some_is_none", "value");
    let some_is_some_value = theorem_symbol("some_is_some", "value");
    let cons_computes_separator = theorem_symbol("intercalate_cons_computes_to_list", "separator");
    let cons_computes_tail = theorem_symbol("intercalate_cons_computes_to_list", "tail");
    let cons_computes_head = theorem_symbol("intercalate_cons_computes_to_list", "head");
    let cons_computes_result = theorem_symbol("intercalate_cons_computes_to_list", "result");
    let computes_separator = theorem_symbol("intercalate_computes_to_list", "separator");
    let computes_lists = theorem_symbol("intercalate_computes_to_list", "lists");
    let computes_result = theorem_symbol("intercalate_computes_to_list", "result");

    assert_eq!(
        intercalate_nil_source_theorem(),
        intercalate_nil_theorem(nil_separator)
    );
    assert_eq!(
        intercalate_singleton_source_theorem(),
        intercalate_singleton_theorem(singleton_separator, singleton_list)
    );
    assert_eq!(
        intercalate_cons_cons_source_theorem(),
        intercalate_cons_cons_theorem(cons_separator, cons_head, cons_next, cons_tail)
    );
    assert_eq!(
        is_list_value_true_implies_is_list_source_theorem(),
        is_list_value_true_implies_is_list_theorem(list_value)
    );
    assert_eq!(
        all_lists_cons_true_source_theorem(),
        all_lists_cons_true_theorem(all_lists_head, all_lists_tail)
    );
    assert_eq!(none_is_none_source_theorem(), none_is_none_theorem());
    assert_eq!(
        some_is_none_source_theorem(),
        some_is_none_theorem(some_is_none_value)
    );
    assert_eq!(none_is_some_source_theorem(), none_is_some_theorem());
    assert_eq!(
        some_is_some_source_theorem(),
        some_is_some_theorem(some_is_some_value)
    );
    assert_eq!(
        intercalate_cons_computes_to_list_source_theorem(),
        intercalate_cons_computes_to_list_theorem(
            cons_computes_separator,
            cons_computes_tail,
            cons_computes_head,
            cons_computes_result
        )
    );
    assert_eq!(
        intercalate_computes_to_list_source_theorem(),
        intercalate_computes_to_list_theorem(computes_separator, computes_lists, computes_result)
    );
}

#[test]
fn concat_map_theorems_have_expected_shape() {
    assert_eq!(
        concat_map_nil_theorem(FUNCTION),
        forall_where(
            FUNCTION,
            is_value(var(FUNCTION)),
            computes_to(concat_map_call(var(FUNCTION), nil()), nil()),
        )
    );
    assert_eq!(
        concat_map_cons_theorem(FUNCTION, HEAD, TAIL),
        forall_where(
            FUNCTION,
            is_value(var(FUNCTION)),
            forall_where(
                HEAD,
                is_value(var(HEAD)),
                forall_where(
                    TAIL,
                    is_list(var(TAIL)),
                    computes_to(
                        concat_map_call(var(FUNCTION), cons(var(HEAD), var(TAIL))),
                        append_call(
                            apply(var(FUNCTION), var(HEAD)),
                            concat_map_call(var(FUNCTION), var(TAIL)),
                        ),
                    ),
                ),
            ),
        )
    );
    assert_eq!(
        concat_map_computes_to_list_theorem(FUNCTION, VALUE, MAPPED_LIST, X, RESULT),
        forall_where(
            FUNCTION,
            is_value(var(FUNCTION)),
            implies(
                forall_where(
                    VALUE,
                    is_value(var(VALUE)),
                    computes_to_list(MAPPED_LIST, apply(var(FUNCTION), var(VALUE))),
                ),
                forall_where(
                    X,
                    is_list(var(X)),
                    computes_to_list(RESULT, concat_map_call(var(FUNCTION), var(X))),
                ),
            ),
        )
    );
}

#[test]
fn concat_map_source_theorems_have_expected_shape() {
    let nil_function = theorem_symbol("concat_map_nil", "function");
    let cons_function = theorem_symbol("concat_map_cons", "function");
    let cons_head = theorem_symbol("concat_map_cons", "head");
    let cons_tail = theorem_symbol("concat_map_cons", "tail");
    let computes_function = theorem_symbol("concat_map_computes_to_list", "function");
    let computes_value = theorem_symbol("concat_map_computes_to_list", "value");
    let computes_mapped_list = theorem_symbol("concat_map_computes_to_list", "mapped_list");
    let computes_list = theorem_symbol("concat_map_computes_to_list", "list");
    let computes_result = theorem_symbol("concat_map_computes_to_list", "result");

    assert_eq!(
        concat_map_nil_source_theorem(),
        concat_map_nil_theorem(nil_function)
    );
    assert_eq!(
        concat_map_cons_source_theorem(),
        concat_map_cons_theorem(cons_function, cons_head, cons_tail)
    );
    assert_eq!(
        concat_map_computes_to_list_source_theorem(),
        concat_map_computes_to_list_theorem(
            computes_function,
            computes_value,
            computes_mapped_list,
            computes_list,
            computes_result,
        )
    );
}

#[test]
fn fold_right_theorems_have_expected_shape() {
    assert_eq!(
        fold_right_nil_theorem(FUNCTION, INITIAL),
        forall_where(
            FUNCTION,
            is_value(var(FUNCTION)),
            forall_where(
                INITIAL,
                is_value(var(INITIAL)),
                computes_to(
                    fold_right_call(var(FUNCTION), var(INITIAL), nil()),
                    var(INITIAL),
                ),
            ),
        )
    );
    assert_eq!(
        fold_right_cons_theorem(FUNCTION, INITIAL, HEAD, TAIL),
        forall_where(
            FUNCTION,
            is_value(var(FUNCTION)),
            forall_where(
                INITIAL,
                is_value(var(INITIAL)),
                forall_where(
                    HEAD,
                    is_value(var(HEAD)),
                    forall_where(
                        TAIL,
                        is_list(var(TAIL)),
                        computes_to(
                            fold_right_call(
                                var(FUNCTION),
                                var(INITIAL),
                                cons(var(HEAD), var(TAIL)),
                            ),
                            apply(
                                apply(var(FUNCTION), var(HEAD)),
                                fold_right_call(var(FUNCTION), var(INITIAL), var(TAIL)),
                            ),
                        ),
                    ),
                ),
            ),
        )
    );
    assert_eq!(
        fold_right_computes_to_value_theorem(
            FUNCTION,
            INITIAL,
            VALUE,
            ACCUMULATOR,
            FOLDED_VALUE,
            X,
            RESULT,
        ),
        forall_where(
            FUNCTION,
            is_value(var(FUNCTION)),
            forall_where(
                INITIAL,
                is_value(var(INITIAL)),
                implies(
                    forall_where(
                        VALUE,
                        is_value(var(VALUE)),
                        forall_where(
                            ACCUMULATOR,
                            is_value(var(ACCUMULATOR)),
                            exists_where(
                                FOLDED_VALUE,
                                is_value(var(FOLDED_VALUE)),
                                computes_to(
                                    apply(apply(var(FUNCTION), var(VALUE)), var(ACCUMULATOR),),
                                    var(FOLDED_VALUE),
                                ),
                            ),
                        ),
                    ),
                    forall_where(
                        X,
                        is_list(var(X)),
                        exists_where(
                            RESULT,
                            is_value(var(RESULT)),
                            computes_to(
                                fold_right_call(var(FUNCTION), var(INITIAL), var(X)),
                                var(RESULT),
                            ),
                        ),
                    ),
                ),
            ),
        )
    );
}

#[test]
fn fold_right_source_theorems_have_expected_shape() {
    let nil_function = theorem_symbol("fold_right_nil", "function");
    let nil_initial = theorem_symbol("fold_right_nil", "initial");
    let cons_function = theorem_symbol("fold_right_cons", "function");
    let cons_initial = theorem_symbol("fold_right_cons", "initial");
    let cons_head = theorem_symbol("fold_right_cons", "head");
    let cons_tail = theorem_symbol("fold_right_cons", "tail");
    let computes_function = theorem_symbol("fold_right_computes_to_value", "function");
    let computes_initial = theorem_symbol("fold_right_computes_to_value", "initial");
    let computes_value = theorem_symbol("fold_right_computes_to_value", "value");
    let computes_accumulator = theorem_symbol("fold_right_computes_to_value", "accumulator");
    let computes_folded_value = theorem_symbol("fold_right_computes_to_value", "folded_value");
    let computes_list = theorem_symbol("fold_right_computes_to_value", "list");
    let computes_result = theorem_symbol("fold_right_computes_to_value", "result");

    assert_eq!(
        fold_right_nil_source_theorem(),
        fold_right_nil_theorem(nil_function, nil_initial)
    );
    assert_eq!(
        fold_right_cons_source_theorem(),
        fold_right_cons_theorem(cons_function, cons_initial, cons_head, cons_tail)
    );
    assert_eq!(
        fold_right_computes_to_value_source_theorem(),
        fold_right_computes_to_value_theorem(
            computes_function,
            computes_initial,
            computes_value,
            computes_accumulator,
            computes_folded_value,
            computes_list,
            computes_result,
        )
    );
}

#[test]
fn fold_left_theorems_have_expected_shape() {
    assert_eq!(
        fold_left_nil_theorem(FUNCTION, INITIAL),
        forall_where(
            FUNCTION,
            is_value(var(FUNCTION)),
            forall_where(
                INITIAL,
                is_value(var(INITIAL)),
                computes_to(
                    fold_left_call(var(FUNCTION), var(INITIAL), nil()),
                    var(INITIAL),
                ),
            ),
        )
    );
    assert_eq!(
        fold_left_cons_theorem(FUNCTION, INITIAL, HEAD, TAIL),
        forall_where(
            FUNCTION,
            is_value(var(FUNCTION)),
            forall_where(
                INITIAL,
                is_value(var(INITIAL)),
                forall_where(
                    HEAD,
                    is_value(var(HEAD)),
                    forall_where(
                        TAIL,
                        is_list(var(TAIL)),
                        computes_to(
                            fold_left_call(var(FUNCTION), var(INITIAL), cons(var(HEAD), var(TAIL)),),
                            fold_left_call(
                                var(FUNCTION),
                                apply(apply(var(FUNCTION), var(INITIAL)), var(HEAD)),
                                var(TAIL),
                            ),
                        ),
                    ),
                ),
            ),
        )
    );
    assert_eq!(
        fold_left_computes_to_value_theorem(
            FUNCTION,
            ACCUMULATOR,
            VALUE,
            FOLDED_VALUE,
            X,
            INITIAL,
            RESULT,
        ),
        forall_where(
            FUNCTION,
            is_value(var(FUNCTION)),
            implies(
                forall_where(
                    ACCUMULATOR,
                    is_value(var(ACCUMULATOR)),
                    forall_where(
                        VALUE,
                        is_value(var(VALUE)),
                        exists_where(
                            FOLDED_VALUE,
                            is_value(var(FOLDED_VALUE)),
                            computes_to(
                                apply(apply(var(FUNCTION), var(ACCUMULATOR)), var(VALUE),),
                                var(FOLDED_VALUE),
                            ),
                        ),
                    ),
                ),
                forall_where(
                    X,
                    is_list(var(X)),
                    forall_where(
                        INITIAL,
                        is_value(var(INITIAL)),
                        exists_where(
                            RESULT,
                            is_value(var(RESULT)),
                            computes_to(
                                fold_left_call(var(FUNCTION), var(INITIAL), var(X)),
                                var(RESULT),
                            ),
                        ),
                    ),
                ),
            ),
        )
    );
}

#[test]
fn fold_left_source_theorems_have_expected_shape() {
    let nil_function = theorem_symbol("fold_left_nil", "function");
    let nil_initial = theorem_symbol("fold_left_nil", "initial");
    let cons_function = theorem_symbol("fold_left_cons", "function");
    let cons_initial = theorem_symbol("fold_left_cons", "initial");
    let cons_head = theorem_symbol("fold_left_cons", "head");
    let cons_tail = theorem_symbol("fold_left_cons", "tail");
    let computes_function = theorem_symbol("fold_left_computes_to_value", "function");
    let computes_accumulator = theorem_symbol("fold_left_computes_to_value", "accumulator");
    let computes_value = theorem_symbol("fold_left_computes_to_value", "value");
    let computes_folded_value = theorem_symbol("fold_left_computes_to_value", "folded_value");
    let computes_list = theorem_symbol("fold_left_computes_to_value", "list");
    let computes_initial = theorem_symbol("fold_left_computes_to_value", "initial");
    let computes_result = theorem_symbol("fold_left_computes_to_value", "result");

    assert_eq!(
        fold_left_nil_source_theorem(),
        fold_left_nil_theorem(nil_function, nil_initial)
    );
    assert_eq!(
        fold_left_cons_source_theorem(),
        fold_left_cons_theorem(cons_function, cons_initial, cons_head, cons_tail)
    );
    assert_eq!(
        fold_left_computes_to_value_source_theorem(),
        fold_left_computes_to_value_theorem(
            computes_function,
            computes_accumulator,
            computes_value,
            computes_folded_value,
            computes_list,
            computes_initial,
            computes_result,
        )
    );
}

#[test]
fn zip_theorems_have_expected_shape() {
    assert_eq!(
        zip_left_nil_theorem(RIGHT_LIST),
        forall_where(
            RIGHT_LIST,
            is_list(var(RIGHT_LIST)),
            computes_to(zip_call(nil(), var(RIGHT_LIST)), nil()),
        )
    );
    assert_eq!(
        zip_right_nil_theorem(X),
        forall_where(
            X,
            is_list(var(X)),
            computes_to(zip_call(var(X), nil()), nil()),
        )
    );
    assert_eq!(
        zip_cons_theorem(LEFT_HEAD, LEFT_TAIL, RIGHT_HEAD, RIGHT_TAIL),
        forall_where(
            LEFT_HEAD,
            is_value(var(LEFT_HEAD)),
            forall_where(
                LEFT_TAIL,
                is_list(var(LEFT_TAIL)),
                forall_where(
                    RIGHT_HEAD,
                    is_value(var(RIGHT_HEAD)),
                    forall_where(
                        RIGHT_TAIL,
                        is_list(var(RIGHT_TAIL)),
                        computes_to(
                            zip_call(
                                cons(var(LEFT_HEAD), var(LEFT_TAIL)),
                                cons(var(RIGHT_HEAD), var(RIGHT_TAIL)),
                            ),
                            cons(
                                pair(var(LEFT_HEAD), var(RIGHT_HEAD)),
                                zip_call(var(LEFT_TAIL), var(RIGHT_TAIL)),
                            ),
                        ),
                    ),
                ),
            ),
        )
    );
    assert_eq!(
        zip_computes_to_list_theorem(X, RIGHT_LIST, RESULT),
        forall_where(
            X,
            is_list(var(X)),
            forall_where(
                RIGHT_LIST,
                is_list(var(RIGHT_LIST)),
                computes_to_list(RESULT, zip_call(var(X), var(RIGHT_LIST))),
            ),
        )
    );
}

#[test]
fn zip_source_theorems_have_expected_shape() {
    let left_nil_right = theorem_symbol("zip_left_nil", "right");
    let right_nil_left = theorem_symbol("zip_right_nil", "left");
    let cons_left_head = theorem_symbol("zip_cons", "left_head");
    let cons_left_tail = theorem_symbol("zip_cons", "left_tail");
    let cons_right_head = theorem_symbol("zip_cons", "right_head");
    let cons_right_tail = theorem_symbol("zip_cons", "right_tail");
    let computes_left = theorem_symbol("zip_computes_to_list", "left");
    let computes_right = theorem_symbol("zip_computes_to_list", "right");
    let computes_result = theorem_symbol("zip_computes_to_list", "result");

    assert_eq!(
        zip_left_nil_source_theorem(),
        zip_left_nil_theorem(left_nil_right)
    );
    assert_eq!(
        zip_right_nil_source_theorem(),
        zip_right_nil_theorem(right_nil_left)
    );
    assert_eq!(
        zip_cons_source_theorem(),
        zip_cons_theorem(
            cons_left_head,
            cons_left_tail,
            cons_right_head,
            cons_right_tail,
        )
    );
    assert_eq!(
        zip_computes_to_list_source_theorem(),
        zip_computes_to_list_theorem(computes_left, computes_right, computes_result)
    );
}

#[test]
fn unzip_theorems_have_expected_shape() {
    assert_eq!(
        unzip_nil_theorem(),
        computes_to(unzip_call(nil()), pair(nil(), nil()))
    );
    assert_eq!(
        unzip_cons_theorem(LEFT_HEAD, RIGHT_HEAD, TAIL),
        forall_where(
            LEFT_HEAD,
            is_value(var(LEFT_HEAD)),
            forall_where(
                RIGHT_HEAD,
                is_value(var(RIGHT_HEAD)),
                forall_where(
                    TAIL,
                    is_list(var(TAIL)),
                    computes_to(
                        unzip_call(cons(pair(var(LEFT_HEAD), var(RIGHT_HEAD)), var(TAIL))),
                        pair(
                            cons(var(LEFT_HEAD), head_call(unzip_call(var(TAIL)))),
                            cons(var(RIGHT_HEAD), head_call(tail_call(unzip_call(var(TAIL)))),),
                        ),
                    ),
                ),
            ),
        )
    );
}

#[test]
fn unzip_source_theorems_have_expected_shape() {
    let cons_left = theorem_symbol("unzip_cons", "left");
    let cons_right = theorem_symbol("unzip_cons", "right");
    let cons_tail = theorem_symbol("unzip_cons", "tail");

    assert_eq!(unzip_nil_source_theorem(), unzip_nil_theorem());
    assert_eq!(
        unzip_cons_source_theorem(),
        unzip_cons_theorem(cons_left, cons_right, cons_tail)
    );
}

#[test]
fn zip_with_theorems_have_expected_shape() {
    assert_eq!(
        zip_with_left_nil_theorem(FUNCTION, RIGHT_LIST),
        forall_where(
            FUNCTION,
            is_value(var(FUNCTION)),
            forall_where(
                RIGHT_LIST,
                is_list(var(RIGHT_LIST)),
                computes_to(zip_with_call(var(FUNCTION), nil(), var(RIGHT_LIST)), nil()),
            ),
        )
    );
    assert_eq!(
        zip_with_right_nil_theorem(FUNCTION, X),
        forall_where(
            FUNCTION,
            is_value(var(FUNCTION)),
            forall_where(
                X,
                is_list(var(X)),
                computes_to(zip_with_call(var(FUNCTION), var(X), nil()), nil()),
            ),
        )
    );
    assert_eq!(
        zip_with_cons_theorem(FUNCTION, LEFT_HEAD, LEFT_TAIL, RIGHT_HEAD, RIGHT_TAIL),
        forall_where(
            FUNCTION,
            is_value(var(FUNCTION)),
            forall_where(
                LEFT_HEAD,
                is_value(var(LEFT_HEAD)),
                forall_where(
                    LEFT_TAIL,
                    is_list(var(LEFT_TAIL)),
                    forall_where(
                        RIGHT_HEAD,
                        is_value(var(RIGHT_HEAD)),
                        forall_where(
                            RIGHT_TAIL,
                            is_list(var(RIGHT_TAIL)),
                            computes_to(
                                zip_with_call(
                                    var(FUNCTION),
                                    cons(var(LEFT_HEAD), var(LEFT_TAIL)),
                                    cons(var(RIGHT_HEAD), var(RIGHT_TAIL)),
                                ),
                                cons(
                                    apply(apply(var(FUNCTION), var(LEFT_HEAD)), var(RIGHT_HEAD),),
                                    zip_with_call(var(FUNCTION), var(LEFT_TAIL), var(RIGHT_TAIL),),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
    );
    assert_eq!(
        zip_with_computes_to_list_theorem(
            FUNCTION,
            LEFT_VALUE,
            RIGHT_VALUE,
            ZIPPED_VALUE,
            X,
            RIGHT_LIST,
            RESULT,
        ),
        forall_where(
            FUNCTION,
            is_value(var(FUNCTION)),
            implies(
                forall_where(
                    LEFT_VALUE,
                    is_value(var(LEFT_VALUE)),
                    forall_where(
                        RIGHT_VALUE,
                        is_value(var(RIGHT_VALUE)),
                        exists_where(
                            ZIPPED_VALUE,
                            is_value(var(ZIPPED_VALUE)),
                            computes_to(
                                apply(apply(var(FUNCTION), var(LEFT_VALUE)), var(RIGHT_VALUE),),
                                var(ZIPPED_VALUE),
                            ),
                        ),
                    ),
                ),
                forall_where(
                    X,
                    is_list(var(X)),
                    forall_where(
                        RIGHT_LIST,
                        is_list(var(RIGHT_LIST)),
                        computes_to_list(
                            RESULT,
                            zip_with_call(var(FUNCTION), var(X), var(RIGHT_LIST)),
                        ),
                    ),
                ),
            ),
        )
    );
}

#[test]
fn zip_with_source_theorems_have_expected_shape() {
    let left_nil_function = theorem_symbol("zip_with_left_nil", "function");
    let left_nil_right = theorem_symbol("zip_with_left_nil", "right");
    let right_nil_function = theorem_symbol("zip_with_right_nil", "function");
    let right_nil_left = theorem_symbol("zip_with_right_nil", "left");
    let cons_function = theorem_symbol("zip_with_cons", "function");
    let cons_left_head = theorem_symbol("zip_with_cons", "left_head");
    let cons_left_tail = theorem_symbol("zip_with_cons", "left_tail");
    let cons_right_head = theorem_symbol("zip_with_cons", "right_head");
    let cons_right_tail = theorem_symbol("zip_with_cons", "right_tail");
    let computes_function = theorem_symbol("zip_with_computes_to_list", "function");
    let computes_left_value = theorem_symbol("zip_with_computes_to_list", "left_value");
    let computes_right_value = theorem_symbol("zip_with_computes_to_list", "right_value");
    let computes_zipped_value = theorem_symbol("zip_with_computes_to_list", "zipped_value");
    let computes_left = theorem_symbol("zip_with_computes_to_list", "left");
    let computes_right = theorem_symbol("zip_with_computes_to_list", "right");
    let computes_result = theorem_symbol("zip_with_computes_to_list", "result");

    assert_eq!(
        zip_with_left_nil_source_theorem(),
        zip_with_left_nil_theorem(left_nil_function, left_nil_right)
    );
    assert_eq!(
        zip_with_right_nil_source_theorem(),
        zip_with_right_nil_theorem(right_nil_function, right_nil_left)
    );
    assert_eq!(
        zip_with_cons_source_theorem(),
        zip_with_cons_theorem(
            cons_function,
            cons_left_head,
            cons_left_tail,
            cons_right_head,
            cons_right_tail,
        )
    );
    assert_eq!(
        zip_with_computes_to_list_source_theorem(),
        zip_with_computes_to_list_theorem(
            computes_function,
            computes_left_value,
            computes_right_value,
            computes_zipped_value,
            computes_left,
            computes_right,
            computes_result,
        )
    );
}
