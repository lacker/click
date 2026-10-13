# Every standard-library symbol

This fixture and the companion regressions named below give every public
declaration in `stdlib/prelude.click` a checked use. The documentation
inventory separately checks that the source registry and library reference
remain complete.

The `authority` resource's restricted empty-population source use is verified
by `authority_establishes_and_retires_empty_stack_population` in
`src/surface/tests/execution_tests.rs`.

The external catalog symbols `memcmp` and `strlen` are verified in
[`strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md`](strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md),
`memcpy` in
[`byte_representation_scalar_copy.md`](byte_representation_scalar_copy.md),
and `memset`'s precondition is checked at a call in
[`c_builtin_memset_header_checks_its_contract.md`](c_builtin_memset_header_checks_its_contract.md).

The external catalog symbol `__click_constant_p_unknown`, the value of the C
builtin `__builtin_constant_p`, is verified in
[`c_builtin_constant_p.md`](c_builtin_constant_p.md).

The modeled-runtime resource `mutex_guard` is verified in
[`mutex_guard_resource_body.md`](mutex_guard_resource_body.md) and
[`mutex_guard_conditional_body.md`](mutex_guard_conditional_body.md).

The modeled-runtime resource `mutex_live` is verified in
[`mutex_live_wrapper.md`](mutex_live_wrapper.md) and
[`mutex_live_contract.md`](mutex_live_contract.md).

The modeled-runtime resource `mutex_use` is verified in
[`mutex_use_contract.md`](mutex_use_contract.md) and
[`mutex_use_mixed.md`](mutex_use_mixed.md).

The modeled-runtime resources `publisher` and `subscriber` are verified in
[`publication_one_shot_handoff.md`](publication_one_shot_handoff.md).

```c filename=stdlib_every_symbol.c
int32 docs_identity(int32 value) {
    return value;
}
```

```click
theorem use_uint32_widened_add_guard_by_integer_bound(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures ((int64)left + (int64)right) <= 4294967295i64 by apply(uint32_widened_add_guard_by_integer_bound(left, right));
}

theorem use_uint32_less_equal_to_integer(left: uint32, right: uint32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by {
        apply(uint32_less_equal_to_integer(left, right));
    }
}
theorem use_uint32_less_equal_of_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by {
        apply(uint32_to_integer_less_equal_implies_less_equal(left, right));
    }
}
theorem use_uint32_equal_of_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right by {
        apply(uint32_to_integer_equal_implies_equal(left, right));
    }
}
theorem use_uint32_to_integer_bounds(value: uint32) {
    ensures 0 <= to_integer(value) by apply(uint32_to_integer_bounds(value));
    ensures to_integer(value) <= 4294967295 by apply(uint32_to_integer_bounds(value));
}
theorem use_int32_to_integer_bounds(value: int32) {
    ensures -2147483648 <= to_integer(value) by apply(int32_to_integer_bounds(value));
    ensures to_integer(value) <= 2147483647 by apply(int32_to_integer_bounds(value));
}
theorem use_int64_to_integer_bounds(value: int64) {
    ensures -9223372036854775808 <= to_integer(value) by apply(int64_to_integer_bounds(value));
    ensures to_integer(value) <= 9223372036854775807 by apply(int64_to_integer_bounds(value));
}
theorem use_uint64_to_integer_bounds(value: uint64) {
    ensures 0 <= to_integer(value) by apply(uint64_to_integer_bounds(value));
    ensures to_integer(value) <= 18446744073709551615 by apply(uint64_to_integer_bounds(value));
}
theorem use_unsigned_reduction(value: uint32, divisor: uint32) {
    requires divisor != 0u32;
    ensures value % divisor < divisor by apply(uint32_remainder_less_than_divisor(value, divisor));
    ensures 0 <= to_integer(value % divisor) by apply(uint32_to_integer_bounds(value % divisor));
    ensures to_integer(value % divisor) < to_integer(divisor) by {
        apply(uint32_remainder_less_than_divisor(value, divisor));
        apply(uint32_less_than_to_integer(value % divisor, divisor));
    }
}
theorem use_uint32_remainder_of_lt(value: uint32, divisor: uint32) {
    requires value < divisor;
    ensures value % divisor == value by apply(uint32_less_than_divisor_implies_remainder_is_value(value, divisor));
}
theorem use_uint32_add_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by apply(uint32_add_to_integer(left, right));
}

theorem use_uint32_subtract_to_integer(left: uint32, right: uint32) {
    requires right <= left;
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        apply(uint32_subtract_to_integer(left, right));
    }
}

theorem use_uint32_nonzero_to_integer(value: uint32) {
    requires value != 0u32;
    ensures to_integer(value) != 0 by apply(uint32_nonzero_to_integer(value));
}
theorem use_uint32_divide_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right)) by apply(uint32_divide_to_integer(left, right));
}
theorem use_uint32_remainder_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right)) by apply(uint32_remainder_to_integer(left, right));
}

theorem use_uint32_mul_to_integer(left: uint32, right: uint32) {
    requires right == 0u32 or left <= 4294967295u32 / right;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by {
        apply(uint32_multiply_to_integer(left, right));
    }
}

theorem use_uint32_mul_guard_by_integer_bound(left: uint32, right: uint32) {
    requires to_integer(left) * to_integer(right) <= 4294967295;
    ensures right == 0u32 or left <= 4294967295u32 / right by {
        apply(uint32_multiply_guard_by_integer_bound(left, right)) using {
            to_integer(left) * to_integer(right) <= 4294967295;
        }
    }
}

theorem use_uint64_add_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) + to_integer(right) <= 18446744073709551615;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by apply(uint64_add_to_integer(left, right));
}

theorem use_uint64_multiply_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) * to_integer(right) <= 18446744073709551615;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by apply(uint64_multiply_to_integer(left, right));
}

theorem use_uint64_subtract_to_integer(left: uint64, right: uint64) {
    requires to_integer(right) <= to_integer(left);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by apply(uint64_subtract_to_integer(left, right));
}

theorem use_uint64_divide_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right)) by apply(uint64_divide_to_integer(left, right));
}

theorem use_uint64_remainder_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right)) by apply(uint64_remainder_to_integer(left, right));
}

theorem use_uint64_less_equal_to_integer(left: uint64, right: uint64) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by apply(uint64_less_equal_to_integer(left, right));
}

theorem use_uint64_less_equal_of_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by apply(uint64_to_integer_less_equal_implies_less_equal(left, right));
}

theorem use_uint64_less_than_to_integer(left: uint64, right: uint64) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by apply(uint64_less_than_to_integer(left, right));
}

theorem use_uint64_less_than_of_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) < to_integer(right);
    ensures left < right by apply(uint64_to_integer_less_than_implies_less_than(left, right));
}

theorem use_uint32_pack_u16_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high) by apply(uint32_pack_uint16_to_integer(low, high));
}

theorem use_uint32_pack_u16_high_first_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer((high << 16) | low) == to_integer(low) + 65536 * to_integer(high) by apply(uint32_pack_uint16_high_first_to_integer(low, high));
}

theorem use_uint32_unpack_u16_low(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures (((high << 16) | low) & 65535u32) == low by apply(uint32_unpack_uint16_low(low, high));
}

theorem use_uint32_unpack_u16_high(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures ((((high << 16) | low) >> 16) & 65535u32) == high by apply(uint32_unpack_uint16_high(low, high));
}

theorem use_uint64_pack_u16_to_integer(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high) by apply(uint64_pack_uint16_to_integer(low, high));
}

theorem use_uint64_not_greater_equal_of_less_than(left: uint64, right: uint64) {
    requires left < right;
    ensures not (left >= right) by apply(uint64_less_than_implies_not_greater_equal(left, right));
}

theorem use_uint64_equal_of_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) == to_integer(right);
    ensures left == right by apply(uint64_to_integer_equal_implies_equal(left, right));
}

theorem use_int64_add_defined_by_integer_bounds(left: int64, right: int64) {
    requires to_integer(left) + to_integer(right) >= -9223372036854775808;
    requires to_integer(left) + to_integer(right) <= 9223372036854775807;
    ensures defined(left + right) by apply(int64_add_defined_by_integer_bounds(left, right));
}

theorem use_int64_subtract_defined_by_integer_bounds(left: int64, right: int64) {
    requires to_integer(left) - to_integer(right) >= -9223372036854775808;
    requires to_integer(left) - to_integer(right) <= 9223372036854775807;
    ensures defined(left - right) by apply(int64_subtract_defined_by_integer_bounds(left, right));
}

theorem use_int64_less_than_of_to_integer(left: int64, right: int64) {
    requires to_integer(left) < to_integer(right);
    ensures left < right by apply(int64_to_integer_less_than_implies_less_than(left, right));
}

theorem use_int64_less_than_to_integer(left: int64, right: int64) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by apply(int64_less_than_to_integer(left, right));
}

theorem use_int64_greater_equal_to_integer(left: int64, right: int64) {
    requires left >= right;
    ensures to_integer(left) >= to_integer(right) by apply(int64_greater_equal_to_integer(left, right));
}

theorem use_floor_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires r < 0 implies value == q + -1;
    requires 0 <= r implies value == q;
    ensures value * d <= n by apply(integer_floor_from_remainder(n, d, q, r, value));
    ensures n < (value + 1) * d by apply(integer_floor_from_remainder(n, d, q, r, value));
}
theorem use_ceiling_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires 0 < r implies value == q + 1;
    requires r <= 0 implies value == q;
    ensures n <= value * d by apply(integer_ceiling_from_remainder(n, d, q, r, value));
    ensures (value + -1) * d < n by apply(integer_ceiling_from_remainder(n, d, q, r, value));
}
theorem use_multiply_add(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by apply(integer_multiply_add(a, b, c));
}
theorem check_truncation_identity(n: Integer, d: Integer) {
    requires d != 0;
    ensures n == truncating_quotient(n, d) * d + truncating_remainder(n, d) by {
        apply(integer_truncation_identity(n, d));
    }
}

theorem check_positive_divisor_remainder_lower(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures 1 - d <= truncating_remainder(n, d) by {
        apply(integer_positive_divisor_remainder_lower(n, d));
    }
}

theorem check_positive_divisor_remainder_upper(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures truncating_remainder(n, d) <= d - 1 by {
        apply(integer_positive_divisor_remainder_upper(n, d));
    }
}

theorem check_nonnegative_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 <= n;
    ensures 0 <= truncating_remainder(n, d) by {
        apply(integer_nonnegative_dividend_remainder(n, d));
    }
}

theorem check_nonpositive_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires n <= 0;
    ensures truncating_remainder(n, d) <= 0 by {
        apply(integer_nonpositive_dividend_remainder(n, d));
    }
}
theorem exact64_sum(left: int64, right: int64) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        apply(int64_add_to_integer(left, right));
    }
}
theorem exact64_difference(left: int64, right: int64) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        apply(int64_subtract_to_integer(left, right));
    }
}

theorem integer_bounds_establish_c_add_safety(left: int32, right: int32) {
    requires to_integer(left) + to_integer(right) >= -2147483648;
    requires to_integer(left) + to_integer(right) <= 2147483647;
    ensures defined(left + right) by {
        apply(int32_add_defined_by_integer_bounds(left, right));
    }
}

theorem integer_bounds_establish_c_subtract_safety(left: int32, right: int32) {
    requires to_integer(left) - to_integer(right) >= -2147483648;
    requires to_integer(left) - to_integer(right) <= 2147483647;
    ensures defined(left - right) by {
        apply(int32_subtract_defined_by_integer_bounds(left, right));
    }
}

theorem integer_add_bridge(left: int32, right: int32) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        apply(int32_add_to_integer(left, right));
    }
}

theorem integer_equality_bridge(left: int32, right: int32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right by {
        apply(int32_to_integer_equal_implies_equal(left, right));
    }
}

theorem reflect32(left: int32, right: int32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by apply(int32_to_integer_less_equal_implies_less_equal(left, right));
}
theorem preserve64(left: int64, right: int64) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by apply(int64_less_equal_to_integer(left, right));
}
theorem reflect64(left: int64, right: int64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by apply(int64_to_integer_less_equal_implies_less_equal(left, right));
}
theorem equal64(left: int64, right: int64) {
    requires to_integer(left) == to_integer(right);
    ensures left == right by apply(int64_to_integer_equal_implies_equal(left, right));
}

theorem integer_order_bridge(left: int32, right: int32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by {
        apply(int32_less_equal_to_integer(left, right));
    }
}

theorem integer_strict_order_bridge(left: int32, right: int32) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by {
        apply(int32_less_than_to_integer(left, right));
    }
}

theorem integer_subtract_bridge(left: int32, right: int32) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        apply(int32_subtract_to_integer(left, right));
    }
}

theorem builtin_nat_integer_laws(n: Nat) {
    ensures to_integer(Nat::Zero) == 0 by apply(nat_integer_zero());
    ensures to_integer(Nat::Succ(n)) == to_integer(n) + 1 by apply(nat_integer_succ(n));
    ensures to_integer(n) >= 0 by apply(nat_integer_nonnegative(n));
    ensures to_nat(to_integer(n)) == n by apply(nat_integer_round_trip(n));
    ensures to_nat(0) == Nat::Zero by apply(integer_to_nat_zero());
}

theorem builtin_integer_nat_laws(z: Integer) {
    requires z >= 0;
    ensures to_integer(to_nat(z)) == z by apply(integer_nat_round_trip(z));
}

theorem nat_laws(a: Nat, b: Nat, c: Nat) {
    ensures to_integer(nat_add(a, b)) == to_integer(a) + to_integer(b) by apply(nat_integer_add(a, b));
    ensures nat_add(Nat::Zero, a) == a by apply(nat_add_left_identity(a));
    ensures nat_add(a, Nat::Zero) == a by apply(nat_add_right_identity(a));
    ensures nat_add(Nat::Succ(a), b) == Nat::Succ(nat_add(a, b)) by apply(nat_add_succ_left(a, b));
    ensures nat_add(a, Nat::Succ(b)) == Nat::Succ(nat_add(a, b)) by apply(nat_add_succ_right(a, b));
    ensures nat_add(nat_add(a, b), c) == nat_add(a, nat_add(b, c)) by apply(nat_add_associative(a, b, c));
    ensures nat_add(a, b) == nat_add(b, a) by apply(nat_add_commutative(a, b));
}

theorem one_plus_one() {
    ensures nat_add(Nat::Succ(Nat::Zero), Nat::Succ(Nat::Zero))
        == Nat::Succ(Nat::Succ(Nat::Zero)) by {
        unfold(nat_add(Nat::Succ(Nat::Zero), Nat::Succ(Nat::Zero)));
        unfold(nat_add(Nat::Zero, Nat::Succ(Nat::Zero)));
        simp();
    }
}

theorem length_laws<T>(head: T, xs: List<T>, ys: List<T>) {
    ensures list_length(List<T>::Nil) == Nat::Zero by {
        apply(list_length_nil(List<T>::Nil));
    }
    ensures list_length(List<T>::Cons(head, xs)) == Nat::Succ(list_length(xs)) by {
        apply(list_length_cons(head, xs));
    }
    ensures list_length(list_append(xs, ys)) == nat_add(list_length(xs), list_length(ys)) by {
        apply(list_length_append(xs, ys));
    }
}

theorem nested_length(xs: List<List<int32>>, ys: List<List<int32>>) {
    ensures list_length(list_append(xs, ys)) == nat_add(list_length(xs), list_length(ys)) by {
        apply(list_length_append(xs, ys));
    }
}

theorem singleton_length(value: int32) {
    ensures list_length(List<int32>::Cons(value, List<int32>::Nil)) == Nat::Succ(Nat::Zero) by {
        unfold(list_length(List<int32>::Cons(value, List<int32>::Nil)));
        unfold(list_length(List<int32>::Nil));
        simp();
    }
}

verifying "stdlib_every_symbol.c";

theorem list_laws(xs: List<int32>, ys: List<int32>, zs: List<int32>, value: int32) {
    ensures list_contains(list_append(xs, ys), value)
        == if list_contains(xs, value) == 1 { 1 } else { list_contains(ys, value) } by {
        apply(list_contains_append(xs, ys, value));
    }
    ensures list_append(List<int32>::Nil, xs) == xs by {
        apply(list_append_left_identity(xs));
        assumption();
    }
    ensures list_append(xs, List<int32>::Nil) == xs by {
        apply(list_append_right_identity(xs));
        assumption();
    }
    ensures list_append(list_append(xs, ys), zs) == list_append(xs, list_append(ys, zs)) by {
        apply(list_append_associative(xs, ys, zs));
        assumption();
    }
    ensures list_contains(List<int32>::Nil, value) == 0 by {
        apply(list_contains_nil(value));
        assumption();
    }
    ensures list_contains(List<int32>::Cons(value, xs), value) == 1 by {
        apply(list_contains_cons(value, xs, value));
        simp();
    }
}

theorem pointer_lists(xs: List<int32*>, ys: List<int32*>, zs: List<int32*>, value: int32*) {
    ensures list_append(list_append(xs, ys), zs) == list_append(xs, list_append(ys, zs)) by {
        apply(list_append_associative(xs, ys, zs));
        assumption();
    }
}

theorem nested_lists(xs: List<List<int32>>) {
    ensures list_append(xs, List<List<int32>>::Nil) == xs by {
        apply(list_append_right_identity(xs));
        assumption();
    }
}
theorem append_constructor(head: int32, tail: List<int32>, ys: List<int32>) {
    ensures list_append(List<int32>::Cons(head, tail), ys)
        == List<int32>::Cons(head, list_append(tail, ys)) by {
        apply(list_append_cons(head, tail, ys));
    }
}

resource docs_allocation_wrapper(base: int32*, bytes: int32) {
    owns allocation(base, bytes);
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

theorem docs_use_int32_increment_greater_than_lower_bound(value: int32, lower: int32, upper: int32) {
    requires value >= lower;
    requires value < upper;

    ensures value + 1 > lower by {
        apply(int32_increment_greater_than_lower_bound(value, lower, upper));
    }
}

theorem docs_use_int32_increment_preserves_order(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures lower + 1 <= value + 1 by {
        apply(int32_increment_preserves_order(value, lower, upper));
    }
}

theorem docs_use_int32_increment_less_equal_implies_less_than(lower: int32, value: int32) {
    requires lower < lower + 1;
    requires lower + 1 <= value;

    ensures lower < value by {
        apply(int32_increment_less_equal_implies_less_than(lower, value));
    }
}

theorem docs_use_int32_less_than_increment_implies_less_equal(value: int32, upper: int32) {
    requires value < upper + 1;

    ensures value <= upper by {
        apply(int32_less_than_increment_implies_less_equal(value, upper));
    }
}

theorem docs_use_int32_positive_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value by {
        apply(int32_positive_is_nonnegative(value));
    }
}

theorem docs_use_int32_less_than_implies_less_equal(left: int32, right: int32) {
    requires left < right;

    ensures left <= right by {
        apply(int32_less_than_implies_less_equal(left, right));
    }
}

theorem docs_use_int32_less_than_implies_not_equal(left: int32, right: int32) {
    requires left < right;

    ensures left != right by {
        apply(int32_less_than_implies_not_equal(left, right));
    }
}

theorem docs_use_int32_not_less_than_implies_greater_equal(left: int32, right: int32) {
    requires not (left < right);

    ensures left >= right by {
        apply(int32_not_less_than_implies_greater_equal(left, right));
    }
}

theorem docs_use_int32_increment_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(value + 1) by {
        apply(int32_increment_below_max_is_defined(value));
    }
}

theorem docs_use_int32_increment_left_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(1 + value) by {
        apply(int32_increment_left_below_max_is_defined(value));
    }
}

theorem docs_use_int32_increment_left_strictly_increases(value: int32) {
    requires value < 2147483647;

    ensures value < 1 + value by {
        apply(int32_increment_left_strictly_increases(value));
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

theorem docs_use_uint32_positive_predecessor_strictly_decreases(value: uint32) {
    requires 0u32 < value;

    ensures value - 1u32 < value by {
        apply(uint32_positive_predecessor_strictly_decreases(value));
    }
}

theorem docs_use_uint32_increment_upper_bound(value: uint32, upper: uint32) {
    requires value < upper;

    ensures value + 1u32 <= upper by {
        apply(uint32_increment_upper_bound(value, upper));
    }
}

theorem docs_use_uint32_increment_strictly_increases(value: uint32, upper: uint32) {
    requires value < upper;

    ensures value < value + 1u32 by {
        apply(uint32_increment_strictly_increases(value, upper));
    }
}

theorem docs_use_uint32_less_than_implies_positive_difference(value: uint32, upper: uint32) {
    requires value < upper;

    ensures 0u32 < upper - value by {
        apply(uint32_less_than_implies_positive_difference(value, upper));
    }
}

theorem docs_use_uint32_difference_decreases_after_increment(value: uint32, bound: uint32) {
    requires value < bound;

    ensures (0u32 - value) + (bound - 1u32) < (0u32 - value) + bound by {
        apply(uint32_difference_decreases_after_increment(value, bound));
    }
}

theorem docs_use_uint32_less_than_less_equal_transitive(first: uint32, middle: uint32, last: uint32) {
    requires first < middle;
    requires middle <= last;

    ensures first < last by {
        apply(uint32_less_than_less_equal_transitive(first, middle, last));
    }
}

theorem docs_use_uint32_less_equal_less_than_transitive(first: uint32, middle: uint32, last: uint32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last by {
        apply(uint32_less_equal_less_than_transitive(first, middle, last));
    }
}

theorem docs_use_uint32_less_than_transitive(first: uint32, middle: uint32, last: uint32) {
    requires first < middle;
    requires middle < last;

    ensures first < last by {
        apply(uint32_less_than_transitive(first, middle, last));
    }
}

theorem docs_use_uint32_less_equal_transitive(first: uint32, middle: uint32, last: uint32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        apply(uint32_less_equal_transitive(first, middle, last));
    }
}

theorem docs_use_uint64_less_equal_and_not_less_than_implies_equal(left: uint64, right: uint64) {
    requires left <= right;
    requires not left < right;

    ensures left == right by {
        apply(uint64_less_equal_and_not_less_than_implies_equal(left, right));
    }
}

theorem docs_use_uint64_less_than_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first < middle;
    requires middle <= last;

    ensures first < last by {
        apply(uint64_less_than_less_equal_transitive(first, middle, last));
    }
}

theorem docs_use_uint64_less_equal_less_than_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first <= middle;
    requires middle < last;

    ensures first < last by {
        apply(uint64_less_equal_less_than_transitive(first, middle, last));
    }
}

theorem docs_use_uint64_less_than_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first < middle;
    requires middle < last;

    ensures first < last by {
        apply(uint64_less_than_transitive(first, middle, last));
    }
}

theorem docs_use_uint64_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        apply(uint64_less_equal_transitive(first, middle, last));
    }
}

theorem docs_use_int64_less_than_less_equal_transitive(first: int64, middle: int64, last: int64) {
    requires first < middle;
    requires middle <= last;

    ensures first < last by {
        apply(int64_less_than_less_equal_transitive(first, middle, last));
    }
}

theorem docs_use_int64_less_equal_less_than_transitive(first: int64, middle: int64, last: int64) {
    requires first <= middle;
    requires middle < last;

    ensures first < last by {
        apply(int64_less_equal_less_than_transitive(first, middle, last));
    }
}

theorem docs_use_int64_less_than_transitive(first: int64, middle: int64, last: int64) {
    requires first < middle;
    requires middle < last;

    ensures first < last by {
        apply(int64_less_than_transitive(first, middle, last));
    }
}

theorem docs_use_int64_less_equal_transitive(first: int64, middle: int64, last: int64) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        apply(int64_less_equal_transitive(first, middle, last));
    }
}

theorem docs_use_uint32_greater_than_implies_reversed_less_than(greater: uint32, lower: uint32) {
    requires greater > lower;

    ensures lower < greater by {
        apply(uint32_greater_than_implies_reversed_less_than(greater, lower));
    }
}

theorem docs_use_uint32_less_than_implies_reversed_greater_than(lower: uint32, greater: uint32) {
    requires lower < greater;

    ensures greater > lower by {
        apply(uint32_less_than_implies_reversed_greater_than(lower, greater));
    }
}

theorem docs_use_uint32_greater_equal_implies_reversed_less_equal(greater: uint32, lower: uint32) {
    requires greater >= lower;

    ensures lower <= greater by {
        apply(uint32_greater_equal_implies_reversed_less_equal(greater, lower));
    }
}

theorem docs_use_uint32_less_equal_implies_reversed_greater_equal(lower: uint32, greater: uint32) {
    requires lower <= greater;

    ensures greater >= lower by {
        apply(uint32_less_equal_implies_reversed_greater_equal(lower, greater));
    }
}

theorem docs_use_int32_nonnegative_predecessor_upper_bound(value: int32, bound: int32) {
    requires 0 <= value;
    requires value <= bound;

    ensures value - 1 <= bound by {
        apply(int32_nonnegative_predecessor_upper_bound(value, bound));
    }
}

theorem docs_use_int32_less_equal_less_than_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last by {
        apply(int32_less_equal_less_than_transitive(first, middle, last));
    }
}

theorem docs_use_int32_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        apply(int32_less_equal_transitive(first, middle, last));
    }
}

theorem docs_use_int32_less_than_transitive(first: int32, middle: int32, last: int32) {
    requires first < middle;
    requires middle < last;

    ensures first < last by {
        apply(int32_less_than_transitive(first, middle, last));
    }
}

theorem docs_use_int32_less_than_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first < middle;
    requires middle <= last;

    ensures first < last by {
        apply(int32_less_than_less_equal_transitive(first, middle, last));
    }
}

theorem docs_use_int32_greater_equal_transitive(last: int32, middle: int32, first: int32) {
    requires last >= middle;
    requires middle >= first;

    ensures last >= first by {
        apply(int32_greater_equal_transitive(last, middle, first));
    }
}

theorem docs_use_int32_greater_equal_implies_reversed_less_equal(greater: int32, lower: int32) {
    requires greater >= lower;

    ensures lower <= greater by {
        apply(int32_greater_equal_implies_reversed_less_equal(greater, lower));
    }
}

theorem docs_use_int32_less_equal_implies_reversed_greater_equal(lower: int32, greater: int32) {
    requires lower <= greater;

    ensures greater >= lower by {
        apply(int32_less_equal_implies_reversed_greater_equal(lower, greater));
    }
}

theorem docs_use_int32_less_equal_and_not_less_than_implies_equal(left: int32, right: int32) {
    requires left <= right;
    requires not (left < right);

    ensures left == right by {
        apply(int32_less_equal_and_not_less_than_implies_equal(left, right));
    }
}

theorem docs_use_int32_less_equal_and_not_equal_implies_less_than(left: int32, right: int32) {
    requires left <= right;
    requires left != right;

    ensures left < right by {
        apply(int32_less_equal_and_not_equal_implies_less_than(left, right));
    }
}

theorem docs_use_int32_greater_equal_and_not_greater_than_implies_equal(left: int32, right: int32) {
    requires left >= right;
    requires not (left > right);

    ensures left == right by {
        apply(int32_greater_equal_and_not_greater_than_implies_equal(left, right));
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

predicate docs_use_bytes_all_equal(bytes: uint8[], lo: int32, hi: int32, value: uint8) {
    bytes_all_equal(bytes, lo, hi, value)
}

predicate docs_use_bytes_contains(bytes: uint8[], lo: int32, hi: int32, value: uint8) {
    bytes_contains(bytes, lo, hi, value)
}

predicate docs_use_bytes_all_not_equal(bytes: uint8[], lo: int32, hi: int32, value: uint8) {
    bytes_all_not_equal(bytes, lo, hi, value)
}

predicate docs_use_cstr_prefix(bytes: uint8[], len: uint64) {
    cstr_prefix(bytes, len)
}

predicate docs_use_cstr_len(bytes: uint8[], len: uint64) {
    cstr_len(bytes, len)
}

predicate docs_use_cstr(bytes: uint8[]) {
    cstr(bytes)
}

predicate docs_use_cstr_readable_len(bytes: uint8[], len: uint64) {
    cstr_readable_len(bytes, len)
}

theorem docs_use_cstr_readable_len_unique(bytes: uint8[], left: uint64, right: uint64) {
    requires forall (k: uint64) {
        k < left implies bytes[k] != '\0'
    };
    requires bytes[left] == '\0';
    requires forall (k: uint64) {
        k < right implies bytes[k] != '\0'
    };
    requires bytes[right] == '\0';

    ensures left == right by {
        apply(cstr_readable_len_unique(bytes, left, right));
    }
}

predicate docs_use_cstr_readable(bytes: uint8[]) {
    cstr_readable(bytes)
}

predicate docs_use_cstr_bounded(bytes: uint8[], max: uint64) {
    cstr_bounded(bytes, max)
}

theorem docs_use_cstr_len_has_prefix(bytes: uint8[], len: uint64) {
    requires cstr_len(bytes, len);

    ensures cstr_prefix(bytes, len) by {
        apply(cstr_len_has_prefix(bytes, len));
    }
}

theorem docs_use_cstr_len_has_terminator(bytes: uint8[], len: uint64) {
    requires cstr_len(bytes, len);

    ensures bytes[len] == '\0' by {
        apply(cstr_len_has_terminator(bytes, len));
    }
}

theorem docs_use_cstr_len_is_viewable(bytes: uint8[], len: uint64) {
    requires cstr_len(bytes, len);

    ensures viewable(bytes[0..len + 1u64]) by {
        apply(cstr_len_is_viewable(bytes, len));
    }
}
theorem use_integer_to_int8_round_trip(z: Integer) {
    requires z >= -128;
    requires z <= 127;
    ensures to_integer(to_int8(z)) == z by apply(integer_to_int8_round_trip(z));
}

theorem use_integer_to_int16_round_trip(z: Integer) {
    requires z >= -32768;
    requires z <= 32767;
    ensures to_integer(to_int16(z)) == z by apply(integer_to_int16_round_trip(z));
}

theorem use_integer_to_int32_round_trip(z: Integer) {
    requires z >= -2147483648;
    requires z <= 2147483647;
    ensures to_integer(to_int32(z)) == z by apply(integer_to_int32_round_trip(z));
}

theorem use_integer_to_uint8_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 255;
    ensures to_integer(to_uint8(z)) == z by apply(integer_to_uint8_round_trip(z));
}

theorem use_integer_to_uint16_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 65535;
    ensures to_integer(to_uint16(z)) == z by apply(integer_to_uint16_round_trip(z));
}

theorem use_integer_to_uint32_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 4294967295;
    ensures to_integer(to_uint32(z)) == z by apply(integer_to_uint32_round_trip(z));
}

theorem use_integer_to_int64_round_trip(z: Integer) {
    requires z >= -9223372036854775808;
    requires z <= 9223372036854775807;
    ensures to_integer(to_int64(z)) == z by apply(integer_to_int64_round_trip(z));
}

theorem use_integer_to_uint64_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 18446744073709551615;
    ensures to_integer(to_uint64(z)) == z by apply(integer_to_uint64_round_trip(z));
}

theorem use_scaled_quotient(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound * d <= n;
    requires n <= bound * d;
    ensures bound <= truncating_quotient(n, d) by apply(integer_positive_divisor_quotient_lower(n, d, bound));
    ensures truncating_quotient(n, d) <= bound by apply(integer_positive_divisor_quotient_upper(n, d, bound));
}

theorem use_strict_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound < 0;
    requires bound * d < n;
    ensures bound < truncating_quotient(n, d) by apply(integer_positive_divisor_quotient_strict_lower(n, d, bound));
}

theorem use_strict_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 < bound;
    requires n < bound * d;
    ensures truncating_quotient(n, d) < bound by apply(integer_positive_divisor_quotient_strict_upper(n, d, bound));
}

theorem use_lower_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, bound: Integer) {
    requires bound <= q; requires bound * d <= n;
    requires n == q * d + r;
    requires r < 0;
    ensures bound + 1 <= q by apply(integer_lower_correction_bound(n, d, q, r, bound));
}
theorem use_upper_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, bound: Integer) {
    requires q <= bound; requires n <= bound * d;
    requires n == q * d + r;
    requires 0 < r;
    ensures q <= bound + -1 by apply(integer_upper_correction_bound(n, d, q, r, bound));
}

theorem use_multiply_orders(a: Integer, b: Integer, c: Integer) {
 requires a <= b; requires 0 <= c;
 ensures a * c <= b * c by apply(integer_multiply_order_nonnegative(a, b, c));
}
theorem use_reverse_multiply_order(a: Integer, b: Integer, c: Integer) {
 requires a <= b; requires c <= 0;
 ensures b * c <= a * c by apply(integer_multiply_order_nonpositive(a, b, c));
}
theorem use_scaled_product(value: Integer, amount: Integer, size: Integer, lower: Integer, upper: Integer) {
 requires lower <= value; requires value <= upper;
 requires lower <= 0; requires 0 <= upper;
 requires 0 <= amount; requires amount <= size;
 ensures lower * size <= value * amount by apply(integer_scaled_product_bounds(value, amount, size, lower, upper));
 ensures value * amount <= upper * size by apply(integer_scaled_product_bounds(value, amount, size, lower, upper));
}

theorem use_int32_remainder_to_integer(left: int32, right: int32) {
    requires defined(left % right);
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right)) by {
        apply(int32_remainder_to_integer(left, right));
    }
}

```

```expect
pass
```
