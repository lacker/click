# Every standard-library symbol

This fixture gives every public declaration in `stdlib/prelude.click` a
checked use. The documentation inventory separately checks that the fixture's
source registry and the library reference remain complete.

The external catalog symbols `memcpy`, `memcmp`, `memset`, and `strlen` are
verified in `mdtests/stdlib_external_contracts.md`.

```c filename=stdlib_every_symbol.c
int32 docs_identity(int32 value) {
    return value;
}
```

```click
verifying "stdlib_every_symbol.c";

resource docs_allocation_wrapper(base: int32*, bytes: int32) {
    contains allocation(base, bytes);
}

theorem docs_use_int32_increment_upper_bound(value: int32, upper: int32) {
    requires value < upper;

    ensures value + 1 <= upper by {
        apply(int32_increment_upper_bound(value, upper));
    }
}

theorem docs_use_int32_increment_strictly_increases(value: int32, upper: int32) {
    requires value < upper;

    ensures value < value + 1 by {
        apply(int32_increment_strictly_increases(value, upper));
    }
}

theorem docs_use_int32_increment_lower_bound(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures lower <= value + 1 by {
        apply(int32_increment_lower_bound(value, lower, upper));
    }
}

theorem docs_use_int32_increment_greater_equal_lower_bound(value: int32, lower: int32, upper: int32) {
    requires value >= lower;
    requires value < upper;

    ensures value + 1 >= lower by {
        apply(int32_increment_greater_equal_lower_bound(value, lower, upper));
    }
}

theorem docs_use_int32_increment_strict_greater_lower_bound(value: int32, lower: int32, upper: int32) {
    requires value >= lower;
    requires value < upper;

    ensures value + 1 > lower by {
        apply(int32_increment_strict_greater_lower_bound(value, lower, upper));
    }
}

theorem docs_use_int32_increment_preserves_order(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures lower + 1 <= value + 1 by {
        apply(int32_increment_preserves_order(value, lower, upper));
    }
}

theorem docs_use_int32_successor_le_implies_lt(lower: int32, value: int32) {
    requires lower < lower + 1;
    requires lower + 1 <= value;

    ensures lower < value by {
        apply(int32_successor_le_implies_lt(lower, value));
    }
}

theorem docs_use_int32_positive_is_nonnegative(value: int32) {
    requires 1 <= value;

    ensures 0 <= value by {
        apply(int32_positive_is_nonnegative(value));
    }
}

theorem docs_use_int32_lt_implies_le(left: int32, right: int32) {
    requires left < right;

    ensures left <= right by {
        apply(int32_lt_implies_le(left, right));
    }
}

theorem docs_use_int32_not_lt_implies_ge(left: int32, right: int32) {
    requires not (left < right);

    ensures left >= right by {
        apply(int32_not_lt_implies_ge(left, right));
    }
}

theorem docs_use_int32_strictly_positive_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures value >= 0 by {
        apply(int32_strictly_positive_is_nonnegative(value));
    }
}

theorem docs_use_int32_increment_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(value + 1) by {
        apply(int32_increment_below_max_is_defined(value));
    }
}

theorem docs_use_int32_one_plus_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(1 + value) by {
        apply(int32_one_plus_below_max_is_defined(value));
    }
}

theorem docs_use_int32_one_plus_strictly_increases(value: int32) {
    requires value < 2147483647;

    ensures value < 1 + value by {
        apply(int32_one_plus_strictly_increases(value));
    }
}

theorem docs_use_int32_nonnegative_add_within_max_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires value <= 2147483647 - amount;

    ensures defined(value + amount) by {
        apply(int32_nonnegative_add_within_max_is_defined(value, amount));
    }
}

theorem docs_use_int32_nonnegative_subtract_within_value_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires amount <= value;

    ensures defined(value - amount) by {
        apply(int32_nonnegative_subtract_within_value_is_defined(value, amount));
    }
}

theorem docs_use_int32_move_one_from_right_to_left_preserves_sum(
    total: int32,
    left: int32,
    right: int32
) {
    requires 0 <= left;
    requires 1 <= right;
    requires total == left + right;

    ensures total == (left + 1) + (right - 1) by {
        apply(int32_move_one_from_right_to_left_preserves_sum(total, left, right));
    }
}

theorem docs_use_int32_subtract_equal_sum_right_cancels(value: int32, left: int32, amount: int32) {
    requires defined(left + amount) and value == left + amount;
    requires defined(value - amount);

    ensures value - amount == left by {
        apply(int32_subtract_equal_sum_right_cancels(value, left, amount));
    }
}

theorem docs_use_int32_add_nonnegative_right_is_at_least_left(left: int32, right: int32) {
    requires 0 <= right;
    requires defined(left + right);

    ensures left <= left + right by {
        apply(int32_add_nonnegative_right_is_at_least_left(left, right));
    }
}

theorem docs_use_int32_add_nonnegative_left_is_at_least_right(left: int32, right: int32) {
    requires 0 <= left;
    requires defined(left + right);

    ensures right <= left + right by {
        apply(int32_add_nonnegative_left_is_at_least_right(left, right));
    }
}

theorem docs_use_int32_positive_predecessor_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value - 1 by {
        apply(int32_positive_predecessor_is_nonnegative(value));
    }
}

theorem docs_use_int32_above_one_predecessor_is_at_least_one(value: int32) {
    requires 1 < value;

    ensures value - 1 >= 1 by {
        apply(int32_above_one_predecessor_is_at_least_one(value));
    }
}

theorem docs_use_int32_positive_predecessor_strictly_decreases(value: int32) {
    requires 0 < value;

    ensures value - 1 < value by {
        apply(int32_positive_predecessor_strictly_decreases(value));
    }
}

theorem docs_use_int32_nonnegative_predecessor_upper_bound(value: int32, bound: int32) {
    requires 0 <= value;
    requires value <= bound;

    ensures value - 1 <= bound by {
        apply(int32_nonnegative_predecessor_upper_bound(value, bound));
    }
}

theorem docs_use_int32_le_lt_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last by {
        apply(int32_le_lt_transitive(first, middle, last));
    }
}

theorem docs_use_int32_le_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        apply(int32_le_transitive(first, middle, last));
    }
}

theorem docs_use_int32_lt_transitive(first: int32, middle: int32, last: int32) {
    requires first < middle;
    requires middle < last;

    ensures first < last by {
        apply(int32_lt_transitive(first, middle, last));
    }
}

theorem docs_use_int32_lt_le_transitive(first: int32, middle: int32, last: int32) {
    requires first < middle;
    requires middle <= last;

    ensures first < last by {
        apply(int32_lt_le_transitive(first, middle, last));
    }
}

theorem docs_use_int32_ge_transitive(last: int32, middle: int32, first: int32) {
    requires last >= middle;
    requires middle >= first;

    ensures last >= first by {
        apply(int32_ge_transitive(last, middle, first));
    }
}

theorem docs_use_int32_ge_implies_reversed_le(greater: int32, lower: int32) {
    requires greater >= lower;

    ensures lower <= greater by {
        apply(int32_ge_implies_reversed_le(greater, lower));
    }
}

theorem docs_use_int32_le_implies_reversed_ge(lower: int32, greater: int32) {
    requires lower <= greater;

    ensures greater >= lower by {
        apply(int32_le_implies_reversed_ge(lower, greater));
    }
}

theorem docs_use_int32_le_and_not_lt_implies_eq(left: int32, right: int32) {
    requires left <= right;
    requires not (left < right);

    ensures left == right by {
        apply(int32_le_and_not_lt_implies_eq(left, right));
    }
}

theorem docs_use_int32_le_and_neq_implies_lt(left: int32, right: int32) {
    requires left <= right;
    requires left != right;

    ensures left < right by {
        apply(int32_le_and_neq_implies_lt(left, right));
    }
}

theorem docs_use_int32_ge_and_not_gt_implies_eq(left: int32, right: int32) {
    requires left >= right;
    requires not (left > right);

    ensures left == right by {
        apply(int32_ge_and_not_gt_implies_eq(left, right));
    }
}

predicate docs_use_count(p: int32[], lo: int32, hi: int32, x: int32) {
    count(p, lo, hi, x) == count(p, lo, hi, x)
}

predicate docs_use_permutation(a: int32[], b: int32[], lo: int32, hi: int32) {
    permutation(a, b, lo, hi)
}

predicate docs_use_byte_count(bytes: uint8[], lo: int32, hi: int32, value: uint8) {
    byte_count(bytes, lo, hi, value) == byte_count(bytes, lo, hi, value)
}

predicate docs_use_bytes_equal(left: uint8[], left_lo: int32, right: uint8[], right_lo: int32, len: int32) {
    bytes_equal(left, left_lo, right, right_lo, len)
}

predicate docs_use_bytes_equal_range(left: uint8[], right: uint8[], lo: int32, hi: int32) {
    bytes_equal_range(left, right, lo, hi)
}

predicate docs_use_bytes_all_eq(bytes: uint8[], lo: int32, hi: int32, value: uint8) {
    bytes_all_eq(bytes, lo, hi, value)
}

predicate docs_use_bytes_contains(bytes: uint8[], lo: int32, hi: int32, value: uint8) {
    bytes_contains(bytes, lo, hi, value)
}

predicate docs_use_bytes_all_not_eq(bytes: uint8[], lo: int32, hi: int32, value: uint8) {
    bytes_all_not_eq(bytes, lo, hi, value)
}

predicate docs_use_cstr_prefix(bytes: uint8[], len: int32) {
    cstr_prefix(bytes, len)
}

predicate docs_use_cstr_len(bytes: uint8[], len: int32) {
    cstr_len(bytes, len)
}

predicate docs_use_cstr(bytes: uint8[]) {
    cstr(bytes)
}

predicate docs_use_cstr_readable_len(bytes: uint8[], len: int32) {
    cstr_readable_len(bytes, len)
}

theorem docs_use_cstr_readable_len_unique(bytes: uint8[], left: int32, right: int32) {
    requires 0 <= left;
    requires forall (k: int32) {
        0 <= k and k < left implies bytes[k] != '\0'
    };
    requires bytes[left] == '\0';
    requires 0 <= right;
    requires forall (k: int32) {
        0 <= k and k < right implies bytes[k] != '\0'
    };
    requires bytes[right] == '\0';

    ensures left == right by {
        apply(cstr_readable_len_unique(bytes, left, right));
    }
}

predicate docs_use_cstr_readable(bytes: uint8[]) {
    cstr_readable(bytes)
}

predicate docs_use_cstr_bounded(bytes: uint8[], max: int32) {
    cstr_bounded(bytes, max)
}

theorem docs_use_cstr_len_nonnegative(bytes: uint8[], len: int32) {
    requires cstr_len(bytes, len);

    ensures 0 <= len by {
        apply(cstr_len_nonnegative(bytes, len));
    }
}

theorem docs_use_cstr_len_has_prefix(bytes: uint8[], len: int32) {
    requires cstr_len(bytes, len);

    ensures cstr_prefix(bytes, len) by {
        apply(cstr_len_has_prefix(bytes, len));
    }
}

theorem docs_use_cstr_len_has_terminator(bytes: uint8[], len: int32) {
    requires cstr_len(bytes, len);

    ensures bytes_contains(bytes, len, len + 1, '\0') by {
        apply(cstr_len_has_terminator(bytes, len));
    }
}

theorem docs_use_cstr_len_is_loadable(bytes: uint8[], len: int32) {
    requires cstr_len(bytes, len);

    ensures loadable(bytes[0..len + 1]) by {
        apply(cstr_len_is_loadable(bytes, len));
    }
}
```

```expect
pass
```
