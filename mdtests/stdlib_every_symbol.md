# Every standard-library symbol

This fixture and the companion regressions named below give every public
declaration in the `library/` modules a checked use. The documentation
inventory separately checks that the source registry and library reference
remain complete.

The `authority` resource's restricted empty-population source use is verified
by `authority_establishes_and_retires_empty_stack_population` in
`src/surface/tests/execution_tests.rs`.

The representation law `integer::uint32_from_le_bytes` is exercised in
[`integer_uint32_from_le_bytes_initialization.md`](integer_uint32_from_le_bytes_initialization.md).

The separation axiom `separation::separate_restrict` is verified in
[`resource_theorem_parameters.md`](resource_theorem_parameters.md), including
forwarding through a user theorem and application to C struct fields.
The element law `separation::separate_elements` is verified in
[`separation_elements.md`](separation_elements.md) and
[`separation_elements_types.md`](separation_elements_types.md).
The element-address law `separation::distinct_elements` is verified in
[`solve_proves_element_addresses_distinct_from_their_indices.md`](solve_proves_element_addresses_distinct_from_their_indices.md),
explicitly and through `solve`.
The generic range law `separation::contains_subrange` is verified in
[`generic_pointer_theorem_parameters.md`](generic_pointer_theorem_parameters.md),
including nested generic applications and several element widths.
The adjacent-range law `separation::separate_adjacent_ranges` is verified in
[`separation_adjacent_ranges.md`](separation_adjacent_ranges.md).

The rebasing law `separation::contains_rebase` is verified in
[`separation_rebase.md`](separation_rebase.md), with signed and unsigned bounds.
The selected-cell law `separation::contains_element` is verified in
[`separation_element_contains_the_selected_cell.md`](separation_element_contains_the_selected_cell.md),
including signed 32-bit and unsigned 64-bit interval bounds.

The external catalog symbols `memcmp` and `strlen` are verified in
[`strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md`](strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md),
`memcpy` in
[`byte_representation_scalar_copy.md`](byte_representation_scalar_copy.md),
and `memset`'s fill conversion is checked at a call in
[`c_builtin_memset_header_checks_its_contract.md`](c_builtin_memset_header_checks_its_contract.md).

The external catalog symbol `__click_constant_p_unknown`, the value of the C
builtin `__builtin_constant_p`, is verified in
[`c_builtin_constant_p.md`](c_builtin_constant_p.md).

The `WriteAttempt` datatype, `stream` resource and `stdio::write_requests`
function are used by
[`printf_and_fprintf_share_the_streams_write_history.md`](printf_and_fprintf_share_the_streams_write_history.md).
The stream also appears in
[`hosted_stdout_stream_follows_file_pointer_alias.md`](hosted_stdout_stream_follows_file_pointer_alias.md).

The borrowed C-string resource `cstr_at` is verified in
[`cstr_at_view_passes_through_a_call.md`](cstr_at_view_passes_through_a_call.md),
[`cstr_at_opens_and_lends_a_prefix_to_a_copy.md`](cstr_at_opens_and_lends_a_prefix_to_a_copy.md),
and [`cstr_at_fold_refuses_a_wrong_length.md`](cstr_at_fold_refuses_a_wrong_length.md).

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

The unsigned address-word laws are checked in
[`aligned_address_word_library.md`](aligned_address_word_library.md):
`integer::uint64_and_commute`, `integer::uint64_and_associate`,
`integer::uint64_or_commute`, `integer::uint64_and_or`, `integer::uint64_and_zero`,
`integer::uint64_or_zero`, `integer::uint64_or_disjoint`, `integer::uint64_mask_add_low`,
`integer::uint64_mask_add_high`, `integer::uint64_mask_multiple`,
`integer::uint64_mask_keep`, `integer::uint64_mask_add_clear`,
`integer::uint64_add_distinct`, `integer::uint64_or_add_low`, `integer::uint64_mask_subset`,
`integer::uint64_or_masked`, `integer::uint8_pointer_add_address_int32`,
`integer::uint8_pointer_add_address_int64`, `integer::int8_pointer_add_address_int32`,
`integer::int8_pointer_add_address_int64`, `integer::uint16_pointer_add_address_int32`,
`integer::uint16_pointer_add_address_int64`, `integer::int16_pointer_add_address_int32`,
`integer::int16_pointer_add_address_int64`, `integer::uint32_pointer_add_address_int32`,
`integer::uint32_pointer_add_address_int64`, `integer::int32_pointer_add_address_int32`,
`integer::int32_pointer_add_address_int64`, `integer::uint64_pointer_add_address_int32`,
`integer::uint64_pointer_add_address_int64`, `integer::int64_pointer_add_address_int32`,
`integer::int64_pointer_add_address_int64`, `integer::float32_pointer_add_address_int32`,
`integer::float32_pointer_add_address_int64`, `integer::float64_pointer_add_address_int32`,
`integer::float64_pointer_add_address_int64`.

The scalar-pointer translation and association families are checked by the
strict scalar-width replay matrix and
[`pointer_offset_explicit_bridge.md`](pointer_offset_explicit_bridge.md):
`integer::uint8_pointer_translate_int32`,
`integer::uint8_pointer_add_associate_int32`,
`integer::uint8_pointer_translate_uint64`,
`integer::uint8_pointer_add_associate_uint64`,
`integer::int8_pointer_translate_int32`,
`integer::int8_pointer_add_associate_int32`,
`integer::int8_pointer_translate_uint64`,
`integer::int8_pointer_add_associate_uint64`,
`integer::uint16_pointer_translate_int32`,
`integer::uint16_pointer_add_associate_int32`,
`integer::uint16_pointer_translate_uint64`,
`integer::uint16_pointer_add_associate_uint64`,
`integer::int16_pointer_translate_int32`,
`integer::int16_pointer_add_associate_int32`,
`integer::int16_pointer_translate_uint64`,
`integer::int16_pointer_add_associate_uint64`,
`integer::uint32_pointer_translate_int32`,
`integer::uint32_pointer_add_associate_int32`,
`integer::uint32_pointer_translate_uint64`,
`integer::uint32_pointer_add_associate_uint64`,
`integer::int32_pointer_translate_int32`,
`integer::int32_pointer_add_associate_int32`,
`integer::int32_pointer_translate_uint64`,
`integer::int32_pointer_add_associate_uint64`,
`integer::uint64_pointer_translate_int32`,
`integer::uint64_pointer_add_associate_int32`,
`integer::uint64_pointer_translate_uint64`,
`integer::uint64_pointer_add_associate_uint64`,
`integer::int64_pointer_translate_int32`,
`integer::int64_pointer_add_associate_int32`,
`integer::int64_pointer_translate_uint64`,
`integer::int64_pointer_add_associate_uint64`,
`integer::float32_pointer_translate_int32`,
`integer::float32_pointer_add_associate_int32`,
`integer::float32_pointer_translate_uint64`,
`integer::float32_pointer_add_associate_uint64`,
`integer::float64_pointer_translate_int32`,
`integer::float64_pointer_add_associate_int32`,
`integer::float64_pointer_translate_uint64`,
`integer::float64_pointer_add_associate_uint64`.

The derived `integer::nonnegative_remainder_from_reconstruction` law is checked
in [`signed_interval_remainder_reconstruction.md`](signed_interval_remainder_reconstruction.md).

```c filename=stdlib_every_symbol.c
int32 docs_identity(int32 value) {
    return value;
}
```

```click
import click::separation;
import click::integer;
import click::permutation;
import click::cstr;
import click::bytes;
import click::c::stdio;
import click::rust::option;
import click::rust::result;
import click::rust::i8;
import click::rust::i16;
import click::rust::i32;
import click::rust::i64;
import click::rust::isize;
import click::rust::u8;
import click::rust::u16;
import click::rust::u32;
import click::rust::u64;
import click::rust::usize;
import click::rust::vec;
import click::rust::slice;

theorem use_uint32_less_equal_to_integer(left: uint32, right: uint32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by {
        apply(integer::uint32_less_equal_to_integer(left, right));
    }
}
theorem use_uint32_less_equal_of_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by {
        apply(integer::uint32_to_integer_less_equal_implies_less_equal(left, right));
    }
}
theorem use_uint32_equal_of_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right by {
        apply(integer::uint32_to_integer_equal_implies_equal(left, right));
    }
}
theorem use_uint32_to_integer_bounds(value: uint32) {
    ensures 0 <= to_integer(value) by apply(integer::uint32_to_integer_bounds(value));
    ensures to_integer(value) <= 4294967295 by apply(integer::uint32_to_integer_bounds(value));
}
theorem use_unsigned_reduction(value: uint32, divisor: uint32) {
    requires divisor != 0u32;
    ensures value % divisor < divisor by apply(integer::uint32_remainder_less_than_divisor(value, divisor));
    ensures 0 <= to_integer(value % divisor) by apply(integer::uint32_to_integer_bounds(value % divisor));
    ensures to_integer(value % divisor) < to_integer(divisor) by {
        apply(integer::uint32_remainder_less_than_divisor(value, divisor));
    }
}
theorem use_uint32_remainder_of_lt(value: uint32, divisor: uint32) {
    requires value < divisor;
    ensures value % divisor == value by apply(integer::uint32_less_than_divisor_implies_remainder_is_value(value, divisor));
}
theorem use_uint32_add_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by apply(integer::uint32_add_to_integer(left, right));
}

theorem use_uint32_subtract_to_integer(left: uint32, right: uint32) {
    requires right <= left;
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        apply(integer::uint32_subtract_to_integer(left, right));
    }
}

theorem use_uint32_divide_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right)) by apply(integer::uint32_divide_to_integer(left, right));
}
theorem use_uint32_remainder_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right)) by apply(integer::uint32_remainder_to_integer(left, right));
}

theorem use_uint32_mul_to_integer(left: uint32, right: uint32) {
    requires right == 0u32 or left <= 4294967295u32 / right;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by {
        apply(integer::uint32_multiply_to_integer(left, right));
    }
}

theorem use_uint32_mul_guard_by_integer_bound(left: uint32, right: uint32) {
    requires to_integer(left) * to_integer(right) <= 4294967295;
    ensures right == 0u32 or left <= 4294967295u32 / right by {
        apply(integer::uint32_multiply_guard_by_integer_bound(left, right)) using {
            to_integer(left) * to_integer(right) <= 4294967295;
        };
    }
}

theorem use_uint64_add_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) + to_integer(right) <= 18446744073709551615;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by apply(integer::uint64_add_to_integer(left, right));
}

theorem use_uint64_multiply_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) * to_integer(right) <= 18446744073709551615;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by apply(integer::uint64_multiply_to_integer(left, right));
}

theorem use_uint64_product_bound_from_division(x: uint64, y: uint64) {
    requires y != 0u64;
    requires x <= 18446744073709551615u64 / y;
    ensures to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64) by apply(integer::uint64_product_bound_from_division(x, y));
}

theorem use_uint64_subtract_to_integer(left: uint64, right: uint64) {
    requires to_integer(right) <= to_integer(left);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by apply(integer::uint64_subtract_to_integer(left, right));
}

theorem use_uint64_divide_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right)) by apply(integer::uint64_divide_to_integer(left, right));
}

theorem use_uint64_remainder_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right)) by apply(integer::uint64_remainder_to_integer(left, right));
}

theorem use_uint64_less_equal_of_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by apply(integer::uint64_to_integer_less_equal_implies_less_equal(left, right));
}

theorem use_uint32_pack_u16_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high) by apply(integer::uint32_pack_uint16_to_integer(low, high));
}

theorem use_uint32_pack_u16_high_first_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer((high << 16) | low) == to_integer(low) + 65536 * to_integer(high) by apply(integer::uint32_pack_uint16_high_first_to_integer(low, high));
}

theorem use_uint32_unpack_u16_low(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures (((high << 16) | low) & 65535u32) == low by apply(integer::uint32_unpack_uint16_low(low, high));
}

theorem use_uint32_unpack_u16_high(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures ((((high << 16) | low) >> 16) & 65535u32) == high by apply(integer::uint32_unpack_uint16_high(low, high));
}

theorem use_uint64_pack_u16_to_integer(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high) by apply(integer::uint64_pack_uint16_to_integer(low, high));
}

theorem use_uint64_unpack_u16_low(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures ((low | (high << 16)) & 65535u64) == low by apply(integer::uint64_unpack_uint16_low(low, high));
}

theorem use_uint64_unpack_u16_high(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures (((low | (high << 16)) >> 16) & 65535u64) == high by apply(integer::uint64_unpack_uint16_high(low, high));
}

theorem use_uint64_not_greater_equal_of_less_than(left: uint64, right: uint64) {
    requires left < right;
    ensures not (left >= right) by apply(integer::uint64_less_than_implies_not_greater_equal(left, right));
}

theorem use_floor_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires r < 0 implies value == q + -1;
    requires 0 <= r implies value == q;
    ensures value * d <= n by apply(integer::floor_from_remainder(n, d, q, r, value));
    ensures n < (value + 1) * d by apply(integer::floor_from_remainder(n, d, q, r, value));
}
theorem use_ceiling_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires 0 < r implies value == q + 1;
    requires r <= 0 implies value == q;
    ensures n <= value * d by apply(integer::ceiling_from_remainder(n, d, q, r, value));
    ensures (value + -1) * d < n by apply(integer::ceiling_from_remainder(n, d, q, r, value));
}
theorem use_multiply_add(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by apply(integer::multiply_add(a, b, c));
}
theorem check_truncation_identity(n: Integer, d: Integer) {
    requires d != 0;
    ensures n == truncating_quotient(n, d) * d + truncating_remainder(n, d) by {
        apply(integer::truncation_identity(n, d));
    }
}

theorem check_positive_divisor_remainder_lower(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures 1 - d <= truncating_remainder(n, d) by {
        apply(integer::positive_divisor_remainder_lower(n, d));
    }
}

theorem check_positive_divisor_remainder_upper(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures truncating_remainder(n, d) <= d - 1 by {
        apply(integer::positive_divisor_remainder_upper(n, d));
    }
}

theorem check_nonnegative_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 <= n;
    ensures 0 <= truncating_remainder(n, d) by {
        apply(integer::nonnegative_dividend_remainder(n, d));
    }
}

theorem check_nonpositive_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires n <= 0;
    ensures truncating_remainder(n, d) <= 0 by {
        apply(integer::nonpositive_dividend_remainder(n, d));
    }
}
theorem exact64_difference(left: int64, right: int64) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        apply(integer::int64_subtract_to_integer(left, right));
    }
}

theorem integer_bounds_establish_c_add_safety(left: int32, right: int32) {
    requires to_integer(left) + to_integer(right) >= -2147483648;
    requires to_integer(left) + to_integer(right) <= 2147483647;
    ensures defined(left + right) by {
        apply(integer::int32_add_defined_by_integer_bounds(left, right));
    }
}

theorem integer_add_bridge(left: int32, right: int32) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        apply(integer::int32_add_to_integer(left, right));
    }
}

theorem reflect32(left: int32, right: int32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by apply(integer::int32_to_integer_less_equal_implies_less_equal(left, right));
}
theorem reflect64(left: int64, right: int64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by apply(integer::int64_to_integer_less_equal_implies_less_equal(left, right));
}

theorem integer_order_bridge(left: int32, right: int32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by {
        apply(integer::int32_less_equal_to_integer(left, right));
    }
}

theorem integer_subtract_bridge(left: int32, right: int32) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        apply(integer::int32_subtract_to_integer(left, right));
    }
}

theorem builtin_nat_integer_laws(n: Nat) {
    ensures to_integer(Nat::Zero) == 0 by apply(nat::to_integer_zero());
    ensures to_integer(Nat::Succ(n)) == to_integer(n) + 1 by apply(nat::to_integer_succ(n));
    ensures to_integer(n) >= 0 by apply(nat::to_integer_nonnegative(n));
    ensures to_nat(to_integer(n)) == n by apply(nat::to_nat_to_integer(n));
    ensures to_nat(0) == Nat::Zero by apply(nat::to_nat_zero());
}

theorem builtin_integer_nat_laws(z: Integer) {
    requires z >= 0;
    ensures to_integer(to_nat(z)) == z by apply(nat::to_integer_to_nat(z));
}

theorem nat_laws(a: Nat, b: Nat, c: Nat) {
    ensures to_integer(nat::add(a, b)) == to_integer(a) + to_integer(b) by apply(nat::to_integer_add(a, b));
    ensures nat::add(Nat::Zero, a) == a by apply(nat::add_left_identity(a));
    ensures nat::add(a, Nat::Zero) == a by apply(nat::add_right_identity(a));
    ensures nat::add(Nat::Succ(a), b) == Nat::Succ(nat::add(a, b)) by apply(nat::add_succ_left(a, b));
    ensures nat::add(a, Nat::Succ(b)) == Nat::Succ(nat::add(a, b)) by apply(nat::add_succ_right(a, b));
    ensures nat::add(nat::add(a, b), c) == nat::add(a, nat::add(b, c)) by apply(nat::add_associative(a, b, c));
    ensures nat::add(a, b) == nat::add(b, a) by apply(nat::add_commutative(a, b));
}

theorem one_plus_one() {
    ensures nat::add(Nat::Succ(Nat::Zero), Nat::Succ(Nat::Zero))
        == Nat::Succ(Nat::Succ(Nat::Zero)) by {
        unfold(nat::add(Nat::Succ(Nat::Zero), Nat::Succ(Nat::Zero)));
        unfold(nat::add(Nat::Zero, Nat::Succ(Nat::Zero)));
        solve();
    }
}

theorem length_laws<T>(head: T, xs: List<T>, ys: List<T>) {
    ensures list::length(List<T>::Nil) == Nat::Zero by {
        apply(list::length_nil(List<T>::Nil));
    }
    ensures list::length(List<T>::Cons(head, xs)) == Nat::Succ(list::length(xs)) by {
        apply(list::length_cons(head, xs));
    }
    ensures list::length(list::append(xs, ys)) == nat::add(list::length(xs), list::length(ys)) by {
        apply(list::length_append(xs, ys));
    }
}

theorem nested_length(xs: List<List<int32>>, ys: List<List<int32>>) {
    ensures list::length(list::append(xs, ys)) == nat::add(list::length(xs), list::length(ys)) by {
        apply(list::length_append(xs, ys));
    }
}

theorem option_constructors(value: int32) {
    ensures Option<int32>::Some(value) != Option<int32>::None by {
        solve();
    }
}

theorem singleton_length(value: int32) {
    ensures list::length(List<int32>::Cons(value, List<int32>::Nil)) == Nat::Succ(Nat::Zero) by {
        unfold(list::length(List<int32>::Cons(value, List<int32>::Nil)));
        unfold(list::length(List<int32>::Nil));
        solve();
    }
}

verifying "stdlib_every_symbol.c";

theorem list_laws(xs: List<int32>, ys: List<int32>, zs: List<int32>, value: int32) {
    ensures list::contains(list::append(xs, ys), value)
        == if list::contains(xs, value) { true } else { list::contains(ys, value) } by {
        apply(list::contains_append(xs, ys, value));
    }
    ensures list::append(List<int32>::Nil, xs) == xs by {
        apply(list::append_left_identity(xs));
        known();
    }
    ensures list::append(xs, List<int32>::Nil) == xs by {
        apply(list::append_right_identity(xs));
        known();
    }
    ensures list::append(list::append(xs, ys), zs) == list::append(xs, list::append(ys, zs)) by {
        apply(list::append_associative(xs, ys, zs));
        known();
    }
    ensures list::contains(List<int32>::Nil, value) == false by {
        apply(list::contains_nil(value));
        known();
    }
    ensures list::contains(List<int32>::Cons(value, xs), value) by {
        apply(list::contains_cons(value, xs, value));
        solve();
    }
}

theorem pointer_lists(xs: List<int32*>, ys: List<int32*>, zs: List<int32*>, value: int32*) {
    ensures list::append(list::append(xs, ys), zs) == list::append(xs, list::append(ys, zs)) by {
        apply(list::append_associative(xs, ys, zs));
        known();
    }
}

theorem nested_lists(xs: List<List<int32>>) {
    ensures list::append(xs, List<List<int32>>::Nil) == xs by {
        apply(list::append_right_identity(xs));
        known();
    }
}
theorem append_constructor(head: int32, tail: List<int32>, ys: List<int32>) {
    ensures list::append(List<int32>::Cons(head, tail), ys)
        == List<int32>::Cons(head, list::append(tail, ys)) by {
        apply(list::append_cons(head, tail, ys));
    }
}

resource docs_allocation_wrapper(base: int32*, bytes: int32) {
    owns allocation(base, bytes);
}

theorem docs_use_int32_increment_upper_bound(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value + 1) <= to_integer(upper) by {
        apply(integer::int32_increment_upper_bound(value, upper));
    }
}

theorem docs_use_int32_increment_strictly_increases(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value) < to_integer(value + 1) by {
        apply(integer::int32_increment_strictly_increases(value, upper));
    }
}

theorem docs_use_int32_increment_lower_bound(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures to_integer(lower) <= to_integer(value + 1) by {
        apply(integer::int32_increment_lower_bound(value, lower, upper));
    }
}

theorem docs_use_int32_positive_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value by {
        apply(integer::int32_positive_is_nonnegative(value));
    }
}

theorem docs_use_int32_increment_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(value + 1) by {
        apply(integer::int32_increment_below_max_is_defined(value));
    }
}

theorem docs_use_int32_nonnegative_add_within_max_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires to_integer(value) <= to_integer(2147483647 - amount);

    ensures defined(value + amount) by {
        apply(integer::int32_nonnegative_add_within_max_is_defined(value, amount));
    }
}

theorem docs_use_int32_nonnegative_subtract_within_value_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires amount <= value;

    ensures defined(value - amount) by {
        apply(integer::int32_nonnegative_subtract_within_value_is_defined(value, amount));
    }
}

theorem docs_use_int32_positive_predecessor_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= to_integer(value - 1) by {
        apply(integer::int32_positive_predecessor_is_nonnegative(value));
    }
}

theorem docs_use_int32_positive_predecessor_strictly_decreases(value: int32) {
    requires 0 < value;

    ensures to_integer(value - 1) < to_integer(value) by {
        apply(integer::int32_positive_predecessor_strictly_decreases(value));
    }
}

theorem docs_use_uint32_positive_predecessor_strictly_decreases(value: uint32) {
    requires 0u32 < value;

    ensures to_integer(value - 1u32) < to_integer(value) by {
        apply(integer::uint32_positive_predecessor_strictly_decreases(value));
    }
}

theorem docs_use_uint32_increment_upper_bound(value: uint32, upper: uint32) {
    requires value < upper;

    ensures to_integer(value + 1u32) <= to_integer(upper) by {
        apply(integer::uint32_increment_upper_bound(value, upper));
    }
}

theorem docs_use_uint32_less_than_implies_positive_difference(value: uint32, upper: uint32) {
    requires value < upper;

    ensures 0 < to_integer(upper - value) by {
        apply(integer::uint32_less_than_implies_positive_difference(value, upper));
    }
}

theorem docs_use_uint32_difference_decreases_after_increment(value: uint32, bound: uint32) {
    requires value < bound;

    ensures integer::uint32_wrapping_add(integer::uint32_wrapping_sub(0u32, value), integer::uint32_wrapping_sub(bound, 1u32)) < integer::uint32_wrapping_add(integer::uint32_wrapping_sub(0u32, value), bound) by {
        apply(integer::uint32_difference_decreases_after_increment(value, bound));
        solve();
    }
}

theorem docs_use_uint64_less_than_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first < middle;
    requires middle <= last;

    ensures first < last by {
        apply(integer::uint64_less_than_less_equal_transitive(first, middle, last));
    }
}

theorem docs_use_uint64_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        apply(integer::uint64_less_equal_transitive(first, middle, last));
    }
}

theorem docs_use_int32_nonnegative_predecessor_upper_bound(value: int32, bound: int32) {
    requires 0 <= value;
    requires value <= bound;

    ensures to_integer(value - 1) <= to_integer(bound) by {
        apply(integer::int32_nonnegative_predecessor_upper_bound(value, bound));
    }
}

theorem docs_use_int32_less_equal_less_than_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last by {
        apply(integer::int32_less_equal_less_than_transitive(first, middle, last));
    }
}

theorem docs_use_int32_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        apply(integer::int32_less_equal_transitive(first, middle, last));
    }
}

theorem docs_use_int32_less_equal_and_not_less_than_implies_equal(left: int32, right: int32) {
    requires left <= right;
    requires not (left < right);

    ensures left == right by {
        apply(integer::int32_less_equal_and_not_less_than_implies_equal(left, right));
    }
}

theorem docs_use_int32_less_equal_and_not_equal_implies_less_than(left: int32, right: int32) {
    requires left <= right;
    requires left != right;

    ensures left < right by {
        apply(integer::int32_less_equal_and_not_equal_implies_less_than(left, right));
    }
}

predicate docs_use_uint32_wrapping_add(left: uint32, right: uint32) {
    integer::uint32_wrapping_add(left, right) == integer::uint32_wrapping_add(left, right)
}

predicate docs_use_uint32_wrapping_sub(left: uint32, right: uint32) {
    integer::uint32_wrapping_sub(left, right) == integer::uint32_wrapping_sub(left, right)
}

predicate docs_use_uint32_wrapping_mul(left: uint32, right: uint32) {
    integer::uint32_wrapping_mul(left, right) == integer::uint32_wrapping_mul(left, right)
}

predicate docs_use_uint64_wrapping_add(left: uint64, right: uint64) {
    integer::uint64_wrapping_add(left, right) == integer::uint64_wrapping_add(left, right)
}

predicate docs_use_uint64_wrapping_sub(left: uint64, right: uint64) {
    integer::uint64_wrapping_sub(left, right) == integer::uint64_wrapping_sub(left, right)
}

predicate docs_use_uint64_wrapping_mul(left: uint64, right: uint64) {
    integer::uint64_wrapping_mul(left, right) == integer::uint64_wrapping_mul(left, right)
}

predicate docs_use_count(p: int32[], lo: int32, hi: int32, x: int32) {
    permutation::count(p, lo, hi, x) == permutation::count(p, lo, hi, x)
}

predicate docs_use_permutation(a: int32[], b: int32[], lo: int32, hi: int32) {
    permutation::permutation(a, b, lo, hi)
}

predicate docs_use_byte_count(bytes: uint8[], lo: int32, hi: int32, value: uint8) {
    bytes::count(bytes, lo, hi, value) == bytes::count(bytes, lo, hi, value)
}

predicate docs_use_bytes_equal(left: uint8[], left_lo: uint64, right: uint8[], right_lo: uint64, len: uint64) {
    bytes::equal(left, left_lo, right, right_lo, len)
}

predicate docs_use_bytes_equal_range(left: uint8[], right: uint8[], lo: uint64, hi: uint64) {
    bytes::equal_range(left, right, lo, hi)
}

predicate docs_use_bytes_all_equal(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    bytes::all_equal(bytes, lo, hi, value)
}

predicate docs_use_bytes_contains(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    bytes::contains(bytes, lo, hi, value)
}

predicate docs_use_bytes_all_not_equal(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    bytes::all_not_equal(bytes, lo, hi, value)
}

predicate docs_use_cstr_prefix(bytes: uint8[], len: uint64) {
    cstr::prefix(bytes, len)
}

predicate docs_use_cstr_len(bytes: uint8[], len: uint64) {
    cstr::len(bytes, len)
}

predicate docs_use_cstr(bytes: uint8[]) {
    cstr::cstr(bytes)
}

predicate docs_use_cstr_readable_len(bytes: uint8[], len: uint64) {
    cstr::readable_len(bytes, len)
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
        apply(cstr::readable_len_unique(bytes, left, right));
    }
}

predicate docs_use_cstr_readable(bytes: uint8[]) {
    cstr::readable(bytes)
}

predicate docs_use_cstr_bounded(bytes: uint8[], max: uint64) {
    cstr::bounded(bytes, max)
}

theorem docs_use_cstr_len_has_prefix(bytes: uint8[], len: uint64) {
    requires cstr::len(bytes, len);

    ensures cstr::prefix(bytes, len) by {
        apply(cstr::len_has_prefix(bytes, len));
    }
}

theorem docs_use_cstr_len_has_terminator(bytes: uint8[], len: uint64) {
    requires cstr::len(bytes, len);

    ensures bytes[len] == '\0' by {
        apply(cstr::len_has_terminator(bytes, len));
    }
}

theorem docs_use_cstr_len_is_viewable(bytes: uint8[], len: uint64) {
    requires cstr::len(bytes, len);

    ensures viewable(bytes[0..len + 1u64]) by {
        apply(cstr::len_is_viewable(bytes, len));
    }
}
theorem use_integer_to_int8_round_trip(z: Integer) {
    requires z >= -128;
    requires z <= 127;
    ensures to_integer(to_int8(z)) == z by apply(integer::to_int8_round_trip(z));
}

theorem use_integer_to_int16_round_trip(z: Integer) {
    requires z >= -32768;
    requires z <= 32767;
    ensures to_integer(to_int16(z)) == z by apply(integer::to_int16_round_trip(z));
}

theorem use_integer_to_int32_round_trip(z: Integer) {
    requires z >= -2147483648;
    requires z <= 2147483647;
    ensures to_integer(to_int32(z)) == z by apply(integer::to_int32_round_trip(z));
}

theorem use_integer_to_uint8_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 255;
    ensures to_integer(to_uint8(z)) == z by apply(integer::to_uint8_round_trip(z));
}

theorem use_integer_to_uint16_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 65535;
    ensures to_integer(to_uint16(z)) == z by apply(integer::to_uint16_round_trip(z));
}

theorem use_integer_to_uint32_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 4294967295;
    ensures to_integer(to_uint32(z)) == z by apply(integer::to_uint32_round_trip(z));
}

theorem use_integer_to_int64_round_trip(z: Integer) {
    requires z >= -9223372036854775808;
    requires z <= 9223372036854775807;
    ensures to_integer(to_int64(z)) == z by apply(integer::to_int64_round_trip(z));
}

theorem use_integer_to_uint64_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 18446744073709551615;
    ensures to_integer(to_uint64(z)) == z by apply(integer::to_uint64_round_trip(z));
}

theorem use_scaled_quotient(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound * d <= n;
    requires n <= bound * d;
    ensures bound <= truncating_quotient(n, d) by apply(integer::positive_divisor_quotient_lower(n, d, bound));
    ensures truncating_quotient(n, d) <= bound by apply(integer::positive_divisor_quotient_upper(n, d, bound));
}

theorem use_strict_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound < 0;
    requires bound * d < n;
    ensures bound < truncating_quotient(n, d) by apply(integer::positive_divisor_quotient_strict_lower(n, d, bound));
}

theorem use_strict_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 < bound;
    requires n < bound * d;
    ensures truncating_quotient(n, d) < bound by apply(integer::positive_divisor_quotient_strict_upper(n, d, bound));
}

theorem use_lower_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, bound: Integer) {
    requires bound <= q; requires bound * d <= n;
    requires n == q * d + r;
    requires r < 0;
    ensures bound + 1 <= q by apply(integer::lower_correction_bound(n, d, q, r, bound));
}
theorem use_upper_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, bound: Integer) {
    requires q <= bound; requires n <= bound * d;
    requires n == q * d + r;
    requires 0 < r;
    ensures q <= bound + -1 by apply(integer::upper_correction_bound(n, d, q, r, bound));
}

theorem use_multiply_orders(a: Integer, b: Integer, c: Integer) {
 requires a <= b; requires 0 <= c;
 ensures a * c <= b * c by apply(integer::multiply_order_nonnegative(a, b, c));
}
theorem use_reverse_multiply_order(a: Integer, b: Integer, c: Integer) {
 requires a <= b; requires c <= 0;
 ensures b * c <= a * c by apply(integer::multiply_order_nonpositive(a, b, c));
}
theorem use_scaled_product(value: Integer, amount: Integer, size: Integer, lower: Integer, upper: Integer) {
 requires lower <= value; requires value <= upper;
 requires lower <= 0; requires 0 <= upper;
 requires 0 <= amount; requires amount <= size;
 ensures lower * size <= value * amount by apply(integer::scaled_product_bounds(value, amount, size, lower, upper));
 ensures value * amount <= upper * size by apply(integer::scaled_product_bounds(value, amount, size, lower, upper));
}

theorem use_int32_remainder_to_integer(left: int32, right: int32) {
    requires defined(left % right);
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right)) by {
        apply(integer::int32_remainder_to_integer(left, right));
    }
}


theorem use_format_pow10_0() {
    ensures stdio::pow10(0u64) == 1u64 by apply(stdio::pow10_0());
}

theorem use_format_pow10_1() {
    ensures stdio::pow10(1u64) == 10u64 by apply(stdio::pow10_1());
}

theorem use_format_pow10_2() {
    ensures stdio::pow10(2u64) == 100u64 by apply(stdio::pow10_2());
}

theorem use_format_pow10_3() {
    ensures stdio::pow10(3u64) == 1000u64 by apply(stdio::pow10_3());
}

theorem use_format_pow10_4() {
    ensures stdio::pow10(4u64) == 10000u64 by apply(stdio::pow10_4());
}

theorem use_format_pow10_5() {
    ensures stdio::pow10(5u64) == 100000u64 by apply(stdio::pow10_5());
}

theorem use_format_pow10_6() {
    ensures stdio::pow10(6u64) == 1000000u64 by apply(stdio::pow10_6());
}

theorem use_format_pow10_7() {
    ensures stdio::pow10(7u64) == 10000000u64 by apply(stdio::pow10_7());
}

theorem use_format_pow10_8() {
    ensures stdio::pow10(8u64) == 100000000u64 by apply(stdio::pow10_8());
}

theorem use_format_pow10_9() {
    ensures stdio::pow10(9u64) == 1000000000u64 by apply(stdio::pow10_9());
}

theorem use_format_decimal_length_1(v: uint64) {
    requires v < 10u64;
    ensures stdio::decimal_length(v) == 1u64 by apply(stdio::decimal_length_1(v));
}

theorem use_format_decimal_length_2(v: uint64) {
    requires 10u64 <= v;
    requires v < 100u64;
    ensures stdio::decimal_length(v) == 2u64 by apply(stdio::decimal_length_2(v));
}

theorem use_format_decimal_length_3(v: uint64) {
    requires 100u64 <= v;
    requires v < 1000u64;
    ensures stdio::decimal_length(v) == 3u64 by apply(stdio::decimal_length_3(v));
}

theorem use_format_decimal_length_4(v: uint64) {
    requires 1000u64 <= v;
    requires v < 10000u64;
    ensures stdio::decimal_length(v) == 4u64 by apply(stdio::decimal_length_4(v));
}

theorem use_format_decimal_length_5(v: uint64) {
    requires 10000u64 <= v;
    requires v < 100000u64;
    ensures stdio::decimal_length(v) == 5u64 by apply(stdio::decimal_length_5(v));
}

theorem use_format_decimal_length_6(v: uint64) {
    requires 100000u64 <= v;
    requires v < 1000000u64;
    ensures stdio::decimal_length(v) == 6u64 by apply(stdio::decimal_length_6(v));
}

theorem use_format_decimal_length_7(v: uint64) {
    requires 1000000u64 <= v;
    requires v < 10000000u64;
    ensures stdio::decimal_length(v) == 7u64 by apply(stdio::decimal_length_7(v));
}

theorem use_format_decimal_length_8(v: uint64) {
    requires 10000000u64 <= v;
    requires v < 100000000u64;
    ensures stdio::decimal_length(v) == 8u64 by apply(stdio::decimal_length_8(v));
}

theorem use_format_decimal_length_9(v: uint64) {
    requires 100000000u64 <= v;
    requires v < 1000000000u64;
    ensures stdio::decimal_length(v) == 9u64 by apply(stdio::decimal_length_9(v));
}

theorem use_format_decimal_length_10(v: uint64) {
    requires 1000000000u64 <= v;
    requires v < 10000000000u64;
    ensures stdio::decimal_length(v) == 10u64 by apply(stdio::decimal_length_10(v));
}

theorem use_format_pow10_nonzero(e: uint64) {
    requires e < 20u64;
    ensures stdio::pow10(e) != 0u64 by apply(stdio::pow10_nonzero(e));
}

theorem use_format_decimal_digit_power_nonzero(v: uint64, k: uint64) {
    requires k < stdio::decimal_length(v);
    ensures stdio::pow10(stdio::decimal_length(v) - 1u64 - k) != 0u64 by apply(stdio::decimal_digit_power_nonzero(v, k));
}

theorem use_format_decimal_digit_of_length(v: uint64) {
    requires stdio::decimal_length(v) == 2u64;
    ensures stdio::decimal_digit(v, 1u64) == (48u64 + v / stdio::pow10(2u64 - 1u64 - 1u64) % 10u64) as uint8 by {
        apply(stdio::decimal_digit_of_length(v, 2u64, 1u64));
    }
}

theorem use_format_decimal_digit_lower_bound(v: uint64) {
    ensures 48u8 <= stdio::decimal_digit(v, 0u64) by apply(stdio::decimal_digit_lower_bound(v, 0u64));
}

theorem use_format_padded_digit_lower_bound(v: uint64) {
    ensures 48u8 <= stdio::padded_digit(v, 3u64, 48u8, 1u64) by apply(stdio::padded_digit_lower_bound(v, 3u64, 1u64));
}

theorem use_format_padded_digit(v: uint64) {
    requires stdio::padded_length(v, 3u64) == 3u64;
    requires stdio::decimal_length(v) == 1u64;
    ensures stdio::padded_digit(v, 3u64, 48u8, 0u64) == 48u8 by {
        unfold(stdio::padded_digit(v, 3u64, 48u8, 0u64));
        solve();
    }
}

theorem use_format_signed_digit() {
    ensures stdio::signed_digit(-5, 0u64) == 45u8 by {
        unfold(stdio::signed_digit(-5, 0u64));
        solve();
    }
}

theorem use_format_signed_length(v: int32) {
    requires 0 <= v;
    ensures stdio::signed_length(v) == stdio::decimal_length(stdio::magnitude(v)) by {
        have not (v < 0) by { known(); }
        have (if v < 0 { 1u64 + stdio::decimal_length(stdio::magnitude(v)) } else { stdio::decimal_length(stdio::magnitude(v)) }) == stdio::decimal_length(stdio::magnitude(v)) by {
            normalize() using { not (v < 0); };
        }
        unfold(stdio::signed_length(v));
        solve();
    }
}
theorem use_rust_i8_min() {
    ensures i8::min((127i64 as int8), (-128i64 as int8)) == (-128i64 as int8) by {
        unfold(i8::min((127i64 as int8), (-128i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_max() {
    ensures i8::max((127i64 as int8), (-128i64 as int8)) == (127i64 as int8) by {
        unfold(i8::max((127i64 as int8), (-128i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_wrapping_add() {
    ensures i8::wrapping_add((127i64 as int8), (1i64 as int8)) == (-128i64 as int8) by {
        unfold(i8::wrapping_add((127i64 as int8), (1i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_wrapping_sub() {
    ensures i8::wrapping_sub((-128i64 as int8), (1i64 as int8)) == (127i64 as int8) by {
        unfold(i8::wrapping_sub((-128i64 as int8), (1i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_wrapping_mul() {
    ensures i8::wrapping_mul((127i64 as int8), (2i64 as int8)) == (-2i64 as int8) by {
        unfold(i8::wrapping_mul((127i64 as int8), (2i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_saturating_add() {
    ensures i8::saturating_add((127i64 as int8), (1i64 as int8)) == (127i64 as int8) by {
        unfold(i8::saturating_add((127i64 as int8), (1i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_saturating_sub() {
    ensures i8::saturating_sub((-128i64 as int8), (1i64 as int8)) == (-128i64 as int8) by {
        unfold(i8::saturating_sub((-128i64 as int8), (1i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_checked_add() {
    ensures i8::checked_add((127i64 as int8), (1i64 as int8)) == Option<int8>::None by {
        unfold(i8::checked_add((127i64 as int8), (1i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_checked_sub() {
    ensures i8::checked_sub((-128i64 as int8), (1i64 as int8)) == Option<int8>::None by {
        unfold(i8::checked_sub((-128i64 as int8), (1i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_abs_diff() {
    ensures i8::abs_diff((-128i64 as int8), (127i64 as int8)) == (255u32 as uint8) by {
        unfold(i8::abs_diff((-128i64 as int8), (127i64 as int8)));
        solve();
    }
}

theorem use_rust_i8_unsigned_abs() {
    ensures i8::unsigned_abs((-128i64 as int8)) == (128u32 as uint8) by {
        unfold(i8::unsigned_abs((-128i64 as int8)));
        solve();
    }
}

theorem use_rust_i16_min() {
    ensures i16::min((32767i64 as int16), (-32768i64 as int16)) == (-32768i64 as int16) by {
        unfold(i16::min((32767i64 as int16), (-32768i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_max() {
    ensures i16::max((32767i64 as int16), (-32768i64 as int16)) == (32767i64 as int16) by {
        unfold(i16::max((32767i64 as int16), (-32768i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_wrapping_add() {
    ensures i16::wrapping_add((32767i64 as int16), (1i64 as int16)) == (-32768i64 as int16) by {
        unfold(i16::wrapping_add((32767i64 as int16), (1i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_wrapping_sub() {
    ensures i16::wrapping_sub((-32768i64 as int16), (1i64 as int16)) == (32767i64 as int16) by {
        unfold(i16::wrapping_sub((-32768i64 as int16), (1i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_wrapping_mul() {
    ensures i16::wrapping_mul((32767i64 as int16), (2i64 as int16)) == (-2i64 as int16) by {
        unfold(i16::wrapping_mul((32767i64 as int16), (2i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_saturating_add() {
    ensures i16::saturating_add((32767i64 as int16), (1i64 as int16)) == (32767i64 as int16) by {
        unfold(i16::saturating_add((32767i64 as int16), (1i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_saturating_sub() {
    ensures i16::saturating_sub((-32768i64 as int16), (1i64 as int16)) == (-32768i64 as int16) by {
        unfold(i16::saturating_sub((-32768i64 as int16), (1i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_checked_add() {
    ensures i16::checked_add((32767i64 as int16), (1i64 as int16)) == Option<int16>::None by {
        unfold(i16::checked_add((32767i64 as int16), (1i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_checked_sub() {
    ensures i16::checked_sub((-32768i64 as int16), (1i64 as int16)) == Option<int16>::None by {
        unfold(i16::checked_sub((-32768i64 as int16), (1i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_abs_diff() {
    ensures i16::abs_diff((-32768i64 as int16), (32767i64 as int16)) == (65535u32 as uint16) by {
        unfold(i16::abs_diff((-32768i64 as int16), (32767i64 as int16)));
        solve();
    }
}

theorem use_rust_i16_unsigned_abs() {
    ensures i16::unsigned_abs((-32768i64 as int16)) == (32768u32 as uint16) by {
        unfold(i16::unsigned_abs((-32768i64 as int16)));
        solve();
    }
}

theorem use_rust_i32_min() {
    ensures i32::min(2147483647, (-2147483648i64 as int32)) == (-2147483648i64 as int32) by {
        unfold(i32::min(2147483647, (-2147483648i64 as int32)));
        solve();
    }
}

theorem use_rust_i32_max() {
    ensures i32::max(2147483647, (-2147483648i64 as int32)) == 2147483647 by {
        unfold(i32::max(2147483647, (-2147483648i64 as int32)));
        solve();
    }
}

theorem use_rust_i32_wrapping_add() {
    ensures i32::wrapping_add(2147483647, 1) == (-2147483648i64 as int32) by {
        unfold(i32::wrapping_add(2147483647, 1));
        solve();
    }
}

theorem use_rust_i32_wrapping_sub() {
    ensures i32::wrapping_sub((-2147483648i64 as int32), 1) == 2147483647 by {
        unfold(i32::wrapping_sub((-2147483648i64 as int32), 1));
        solve();
    }
}

theorem use_rust_i32_wrapping_mul() {
    ensures i32::wrapping_mul(2147483647, 2) == (-2i64 as int32) by {
        unfold(i32::wrapping_mul(2147483647, 2));
        solve();
    }
}

theorem use_rust_i32_saturating_add() {
    ensures i32::saturating_add(2147483647, 1) == 2147483647 by {
        unfold(i32::saturating_add(2147483647, 1));
        solve();
    }
}

theorem use_rust_i32_saturating_sub() {
    ensures i32::saturating_sub((-2147483648i64 as int32), 1) == (-2147483648i64 as int32) by {
        unfold(i32::saturating_sub((-2147483648i64 as int32), 1));
        solve();
    }
}

theorem use_rust_i32_checked_add() {
    ensures i32::checked_add(2147483647, 1) == Option<int32>::None by {
        unfold(i32::checked_add(2147483647, 1));
        solve();
    }
}

theorem use_rust_i32_checked_sub() {
    ensures i32::checked_sub((-2147483648i64 as int32), 1) == Option<int32>::None by {
        unfold(i32::checked_sub((-2147483648i64 as int32), 1));
        solve();
    }
}

theorem use_rust_i32_abs_diff() {
    ensures i32::abs_diff((-2147483648i64 as int32), 2147483647) == 4294967295u32 by {
        unfold(i32::abs_diff((-2147483648i64 as int32), 2147483647));
        solve();
    }
}

theorem use_rust_i32_unsigned_abs() {
    ensures i32::unsigned_abs((-2147483648i64 as int32)) == 2147483648u32 by {
        unfold(i32::unsigned_abs((-2147483648i64 as int32)));
        solve();
    }
}

theorem use_rust_i64_min() {
    ensures i64::min(9223372036854775807i64, -9223372036854775808i64) == -9223372036854775808i64 by {
        unfold(i64::min(9223372036854775807i64, -9223372036854775808i64));
        solve();
    }
}

theorem use_rust_i64_max() {
    ensures i64::max(9223372036854775807i64, -9223372036854775808i64) == 9223372036854775807i64 by {
        unfold(i64::max(9223372036854775807i64, -9223372036854775808i64));
        solve();
    }
}

theorem use_rust_i64_wrapping_add() {
    ensures i64::wrapping_add(9223372036854775807i64, 1i64) == -9223372036854775808i64 by {
        unfold(i64::wrapping_add(9223372036854775807i64, 1i64));
        solve();
    }
}

theorem use_rust_i64_wrapping_sub() {
    ensures i64::wrapping_sub(-9223372036854775808i64, 1i64) == 9223372036854775807i64 by {
        unfold(i64::wrapping_sub(-9223372036854775808i64, 1i64));
        solve();
    }
}

theorem use_rust_i64_wrapping_mul() {
    ensures i64::wrapping_mul(9223372036854775807i64, 2i64) == -2i64 by {
        unfold(i64::wrapping_mul(9223372036854775807i64, 2i64));
        solve();
    }
}

theorem use_rust_i64_saturating_add() {
    ensures i64::saturating_add(9223372036854775807i64, 1i64) == 9223372036854775807i64 by {
        unfold(i64::saturating_add(9223372036854775807i64, 1i64));
        solve();
    }
}

theorem use_rust_i64_saturating_sub() {
    ensures i64::saturating_sub(-9223372036854775808i64, 1i64) == -9223372036854775808i64 by {
        unfold(i64::saturating_sub(-9223372036854775808i64, 1i64));
        solve();
    }
}

theorem use_rust_i64_checked_add() {
    ensures i64::checked_add(9223372036854775807i64, 1i64) == Option<int64>::None by {
        unfold(i64::checked_add(9223372036854775807i64, 1i64));
        solve();
    }
}

theorem use_rust_i64_checked_sub() {
    ensures i64::checked_sub(-9223372036854775808i64, 1i64) == Option<int64>::None by {
        unfold(i64::checked_sub(-9223372036854775808i64, 1i64));
        solve();
    }
}

theorem use_rust_i64_abs_diff() {
    ensures i64::abs_diff(-9223372036854775808i64, 9223372036854775807i64) == 18446744073709551615u64 by {
        unfold(i64::abs_diff(-9223372036854775808i64, 9223372036854775807i64));
        solve();
    }
}

theorem use_rust_i64_unsigned_abs() {
    ensures i64::unsigned_abs(-9223372036854775808i64) == 9223372036854775808u64 by {
        unfold(i64::unsigned_abs(-9223372036854775808i64));
        solve();
    }
}

theorem use_rust_isize_min() {
    ensures isize::min(9223372036854775807i64, -9223372036854775808i64) == -9223372036854775808i64 by {
        unfold(isize::min(9223372036854775807i64, -9223372036854775808i64));
        solve();
    }
}

theorem use_rust_isize_max() {
    ensures isize::max(9223372036854775807i64, -9223372036854775808i64) == 9223372036854775807i64 by {
        unfold(isize::max(9223372036854775807i64, -9223372036854775808i64));
        solve();
    }
}

theorem use_rust_isize_wrapping_add() {
    ensures isize::wrapping_add(9223372036854775807i64, 1i64) == -9223372036854775808i64 by {
        unfold(isize::wrapping_add(9223372036854775807i64, 1i64));
        solve();
    }
}

theorem use_rust_isize_wrapping_sub() {
    ensures isize::wrapping_sub(-9223372036854775808i64, 1i64) == 9223372036854775807i64 by {
        unfold(isize::wrapping_sub(-9223372036854775808i64, 1i64));
        solve();
    }
}

theorem use_rust_isize_wrapping_mul() {
    ensures isize::wrapping_mul(9223372036854775807i64, 2i64) == -2i64 by {
        unfold(isize::wrapping_mul(9223372036854775807i64, 2i64));
        solve();
    }
}

theorem use_rust_isize_saturating_add() {
    ensures isize::saturating_add(9223372036854775807i64, 1i64) == 9223372036854775807i64 by {
        unfold(isize::saturating_add(9223372036854775807i64, 1i64));
        solve();
    }
}

theorem use_rust_isize_saturating_sub() {
    ensures isize::saturating_sub(-9223372036854775808i64, 1i64) == -9223372036854775808i64 by {
        unfold(isize::saturating_sub(-9223372036854775808i64, 1i64));
        solve();
    }
}

theorem use_rust_isize_checked_add() {
    ensures isize::checked_add(9223372036854775807i64, 1i64) == Option<int64>::None by {
        unfold(isize::checked_add(9223372036854775807i64, 1i64));
        solve();
    }
}

theorem use_rust_isize_checked_sub() {
    ensures isize::checked_sub(-9223372036854775808i64, 1i64) == Option<int64>::None by {
        unfold(isize::checked_sub(-9223372036854775808i64, 1i64));
        solve();
    }
}

theorem use_rust_isize_abs_diff() {
    ensures isize::abs_diff(-9223372036854775808i64, 9223372036854775807i64) == 18446744073709551615u64 by {
        unfold(isize::abs_diff(-9223372036854775808i64, 9223372036854775807i64));
        solve();
    }
}

theorem use_rust_isize_unsigned_abs() {
    ensures isize::unsigned_abs(-9223372036854775808i64) == 9223372036854775808u64 by {
        unfold(isize::unsigned_abs(-9223372036854775808i64));
        solve();
    }
}

theorem use_rust_u8_min() {
    ensures u8::min((255u32 as uint8), (0u32 as uint8)) == (0u32 as uint8) by {
        unfold(u8::min((255u32 as uint8), (0u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_max() {
    ensures u8::max((255u32 as uint8), (0u32 as uint8)) == (255u32 as uint8) by {
        unfold(u8::max((255u32 as uint8), (0u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_wrapping_add() {
    ensures u8::wrapping_add((255u32 as uint8), (1u32 as uint8)) == (0u32 as uint8) by {
        unfold(u8::wrapping_add((255u32 as uint8), (1u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_wrapping_sub() {
    ensures u8::wrapping_sub((0u32 as uint8), (1u32 as uint8)) == (255u32 as uint8) by {
        unfold(u8::wrapping_sub((0u32 as uint8), (1u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_wrapping_mul() {
    ensures u8::wrapping_mul((255u32 as uint8), (2u32 as uint8)) == (254u32 as uint8) by {
        unfold(u8::wrapping_mul((255u32 as uint8), (2u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_saturating_add() {
    ensures u8::saturating_add((255u32 as uint8), (1u32 as uint8)) == (255u32 as uint8) by {
        unfold(u8::saturating_add((255u32 as uint8), (1u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_saturating_sub() {
    ensures u8::saturating_sub((0u32 as uint8), (1u32 as uint8)) == (0u32 as uint8) by {
        unfold(u8::saturating_sub((0u32 as uint8), (1u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_checked_add() {
    ensures u8::checked_add((255u32 as uint8), (1u32 as uint8)) == Option<uint8>::None by {
        unfold(u8::checked_add((255u32 as uint8), (1u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_checked_sub() {
    ensures u8::checked_sub((0u32 as uint8), (1u32 as uint8)) == Option<uint8>::None by {
        unfold(u8::checked_sub((0u32 as uint8), (1u32 as uint8)));
        solve();
    }
}

theorem use_rust_u8_abs_diff() {
    ensures u8::abs_diff((0u32 as uint8), (255u32 as uint8)) == (255u32 as uint8) by {
        unfold(u8::abs_diff((0u32 as uint8), (255u32 as uint8)));
        solve();
    }
}

theorem use_rust_u16_min() {
    ensures u16::min((65535u32 as uint16), (0u32 as uint16)) == (0u32 as uint16) by {
        unfold(u16::min((65535u32 as uint16), (0u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_max() {
    ensures u16::max((65535u32 as uint16), (0u32 as uint16)) == (65535u32 as uint16) by {
        unfold(u16::max((65535u32 as uint16), (0u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_wrapping_add() {
    ensures u16::wrapping_add((65535u32 as uint16), (1u32 as uint16)) == (0u32 as uint16) by {
        unfold(u16::wrapping_add((65535u32 as uint16), (1u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_wrapping_sub() {
    ensures u16::wrapping_sub((0u32 as uint16), (1u32 as uint16)) == (65535u32 as uint16) by {
        unfold(u16::wrapping_sub((0u32 as uint16), (1u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_wrapping_mul() {
    ensures u16::wrapping_mul((65535u32 as uint16), (2u32 as uint16)) == (65534u32 as uint16) by {
        unfold(u16::wrapping_mul((65535u32 as uint16), (2u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_saturating_add() {
    ensures u16::saturating_add((65535u32 as uint16), (1u32 as uint16)) == (65535u32 as uint16) by {
        unfold(u16::saturating_add((65535u32 as uint16), (1u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_saturating_sub() {
    ensures u16::saturating_sub((0u32 as uint16), (1u32 as uint16)) == (0u32 as uint16) by {
        unfold(u16::saturating_sub((0u32 as uint16), (1u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_checked_add() {
    ensures u16::checked_add((65535u32 as uint16), (1u32 as uint16)) == Option<uint16>::None by {
        unfold(u16::checked_add((65535u32 as uint16), (1u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_checked_sub() {
    ensures u16::checked_sub((0u32 as uint16), (1u32 as uint16)) == Option<uint16>::None by {
        unfold(u16::checked_sub((0u32 as uint16), (1u32 as uint16)));
        solve();
    }
}

theorem use_rust_u16_abs_diff() {
    ensures u16::abs_diff((0u32 as uint16), (65535u32 as uint16)) == (65535u32 as uint16) by {
        unfold(u16::abs_diff((0u32 as uint16), (65535u32 as uint16)));
        solve();
    }
}

theorem use_rust_u32_min() {
    ensures u32::min(4294967295u32, 0u32) == 0u32 by {
        unfold(u32::min(4294967295u32, 0u32));
        solve();
    }
}

theorem use_rust_u32_max() {
    ensures u32::max(4294967295u32, 0u32) == 4294967295u32 by {
        unfold(u32::max(4294967295u32, 0u32));
        solve();
    }
}

theorem use_rust_u32_wrapping_add() {
    ensures u32::wrapping_add(4294967295u32, 1u32) == 0u32 by {
        unfold(u32::wrapping_add(4294967295u32, 1u32));
        solve();
    }
}

theorem use_rust_u32_wrapping_sub() {
    ensures u32::wrapping_sub(0u32, 1u32) == 4294967295u32 by {
        unfold(u32::wrapping_sub(0u32, 1u32));
        solve();
    }
}

theorem use_rust_u32_wrapping_mul() {
    ensures u32::wrapping_mul(4294967295u32, 2u32) == 4294967294u32 by {
        unfold(u32::wrapping_mul(4294967295u32, 2u32));
        solve();
    }
}

theorem use_rust_u32_saturating_add() {
    ensures u32::saturating_add(4294967295u32, 1u32) == 4294967295u32 by {
        unfold(u32::saturating_add(4294967295u32, 1u32));
        solve();
    }
}

theorem use_rust_u32_saturating_sub() {
    ensures u32::saturating_sub(0u32, 1u32) == 0u32 by {
        unfold(u32::saturating_sub(0u32, 1u32));
        solve();
    }
}

theorem use_rust_u32_checked_add() {
    ensures u32::checked_add(4294967295u32, 1u32) == Option<uint32>::None by {
        unfold(u32::checked_add(4294967295u32, 1u32));
        solve();
    }
}

theorem use_rust_u32_checked_sub() {
    ensures u32::checked_sub(0u32, 1u32) == Option<uint32>::None by {
        unfold(u32::checked_sub(0u32, 1u32));
        solve();
    }
}

theorem use_rust_u32_abs_diff() {
    ensures u32::abs_diff(0u32, 4294967295u32) == 4294967295u32 by {
        unfold(u32::abs_diff(0u32, 4294967295u32));
        solve();
    }
}

theorem use_rust_u32_multiply_to_integer(left: uint32, right: uint32) {
    requires right == 0u32 or left <= 4294967295u32 / right;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by apply(u32::multiply_to_integer(left, right));
}

theorem use_rust_u64_min() {
    ensures u64::min(18446744073709551615u64, 0u64) == 0u64 by {
        unfold(u64::min(18446744073709551615u64, 0u64));
        solve();
    }
}

theorem use_rust_u64_max() {
    ensures u64::max(18446744073709551615u64, 0u64) == 18446744073709551615u64 by {
        unfold(u64::max(18446744073709551615u64, 0u64));
        solve();
    }
}

theorem use_rust_u64_wrapping_add() {
    ensures u64::wrapping_add(18446744073709551615u64, 1u64) == 0u64 by {
        unfold(u64::wrapping_add(18446744073709551615u64, 1u64));
        solve();
    }
}

theorem use_rust_u64_wrapping_sub() {
    ensures u64::wrapping_sub(0u64, 1u64) == 18446744073709551615u64 by {
        unfold(u64::wrapping_sub(0u64, 1u64));
        solve();
    }
}

theorem use_rust_u64_wrapping_mul() {
    ensures u64::wrapping_mul(18446744073709551615u64, 2u64) == 18446744073709551614u64 by {
        unfold(u64::wrapping_mul(18446744073709551615u64, 2u64));
        solve();
    }
}

theorem use_rust_u64_saturating_add() {
    ensures u64::saturating_add(18446744073709551615u64, 1u64) == 18446744073709551615u64 by {
        unfold(u64::saturating_add(18446744073709551615u64, 1u64));
        solve();
    }
}

theorem use_rust_u64_saturating_sub() {
    ensures u64::saturating_sub(0u64, 1u64) == 0u64 by {
        unfold(u64::saturating_sub(0u64, 1u64));
        solve();
    }
}

theorem use_rust_u64_checked_add() {
    ensures u64::checked_add(18446744073709551615u64, 1u64) == Option<uint64>::None by {
        unfold(u64::checked_add(18446744073709551615u64, 1u64));
        solve();
    }
}

theorem use_rust_u64_checked_sub() {
    ensures u64::checked_sub(0u64, 1u64) == Option<uint64>::None by {
        unfold(u64::checked_sub(0u64, 1u64));
        solve();
    }
}

theorem use_rust_u64_abs_diff() {
    ensures u64::abs_diff(0u64, 18446744073709551615u64) == 18446744073709551615u64 by {
        unfold(u64::abs_diff(0u64, 18446744073709551615u64));
        solve();
    }
}

theorem use_rust_usize_min() {
    ensures usize::min(18446744073709551615u64, 0u64) == 0u64 by {
        unfold(usize::min(18446744073709551615u64, 0u64));
        solve();
    }
}

theorem use_rust_usize_max() {
    ensures usize::max(18446744073709551615u64, 0u64) == 18446744073709551615u64 by {
        unfold(usize::max(18446744073709551615u64, 0u64));
        solve();
    }
}

theorem use_rust_usize_wrapping_add() {
    ensures usize::wrapping_add(18446744073709551615u64, 1u64) == 0u64 by {
        unfold(usize::wrapping_add(18446744073709551615u64, 1u64));
        solve();
    }
}

theorem use_rust_usize_wrapping_sub() {
    ensures usize::wrapping_sub(0u64, 1u64) == 18446744073709551615u64 by {
        unfold(usize::wrapping_sub(0u64, 1u64));
        solve();
    }
}

theorem use_rust_usize_wrapping_mul() {
    ensures usize::wrapping_mul(18446744073709551615u64, 2u64) == 18446744073709551614u64 by {
        unfold(usize::wrapping_mul(18446744073709551615u64, 2u64));
        solve();
    }
}

theorem use_rust_usize_saturating_add() {
    ensures usize::saturating_add(18446744073709551615u64, 1u64) == 18446744073709551615u64 by {
        unfold(usize::saturating_add(18446744073709551615u64, 1u64));
        solve();
    }
}

theorem use_rust_usize_saturating_sub() {
    ensures usize::saturating_sub(0u64, 1u64) == 0u64 by {
        unfold(usize::saturating_sub(0u64, 1u64));
        solve();
    }
}

theorem use_rust_usize_checked_add() {
    ensures usize::checked_add(18446744073709551615u64, 1u64) == Option<uint64>::None by {
        unfold(usize::checked_add(18446744073709551615u64, 1u64));
        solve();
    }
}

theorem use_rust_usize_checked_sub() {
    ensures usize::checked_sub(0u64, 1u64) == Option<uint64>::None by {
        unfold(usize::checked_sub(0u64, 1u64));
        solve();
    }
}

theorem use_rust_usize_abs_diff() {
    ensures usize::abs_diff(0u64, 18446744073709551615u64) == 18446744073709551615u64 by {
        unfold(usize::abs_diff(0u64, 18446744073709551615u64));
        solve();
    }
}

theorem use_rust_usize_product_bound_from_division(x: uint64, y: uint64) {
    requires y != 0u64;
    requires x <= 18446744073709551615u64 / y;
    ensures to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64) by apply(usize::product_bound_from_division(x, y));
}

theorem use_rust_usize_multiply_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) * to_integer(right) <= 18446744073709551615;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by apply(usize::multiply_to_integer(left, right));
}

theorem use_option_unwrap_or(d: int32) {
    ensures option::unwrap_or(Option<int32>::None, d) == d by {
        unfold(option::unwrap_or(Option<int32>::None, d));
        solve();
    }
}

theorem use_result_unwrap_or(d: int32) {
    ensures result::unwrap_or(Result<int32, uint8>::Err(3u8), d) == d by {
        unfold(result::unwrap_or(Result<int32, uint8>::Err(3u8), d));
        solve();
    }
}
theorem use_separation_star(A: Resource, B: Resource, C: Resource, E: Resource) {
    requires separate(A, C);
    requires separate(B, C);
    requires contains(A * B, E);
    ensures separate(E, C) by {
        apply(separation::separate_star(A, B, C)) using {
            separate(A, C); separate(B, C);
        };
        apply(separation::contains_refl(C)) using {};
        apply(separation::separate_restrict(A * B, C, E, C)) using {
            separate(A * B, C); contains(A * B, E); contains(C, C);
        };
    }
}
theorem use_separation_components(A: Resource, B: Resource, C: Resource) {
    ensures contains((A * B) * C, B) by {
        apply(separation::contains_left(A * B, C)) using {};
        apply(separation::contains_right(A, B)) using {};
        apply(separation::contains_trans((A * B) * C, A * B, B)) using {
            contains((A * B) * C, A * B); contains(A * B, B);
        };
    }
}
theorem use_separation_empty(A: Resource) {
    ensures separate(A, separation::emp) by {
        apply(separation::separate_emp(A)) using {};
        apply(separation::separate_symm(separation::emp, A)) using {
            separate(separation::emp, A);
        };
    }
}
theorem use_vec(v: Vec<uint32>, w: Vec<uint32>, x: uint32, i: uint64, j: uint64) {
    requires vec::len(v) < 18446744073709551615u64;
    requires i < vec::len(v);
    requires j < vec::len(v);
    requires i != j;
    requires vec::len(v) == vec::len(w);
    requires forall (k: uint64) { k < vec::len(v) implies vec::get(v, k) == vec::get(w, k) };
    ensures vec::len(vec::push(v, x)) == vec::len(v) + 1 by {
        apply(vec::len_push(v, x));
    }
    ensures vec::get(vec::push(v, x), vec::len(v)) == x by {
        apply(vec::get_push_last(v, x));
    }
    ensures vec::get(vec::push(v, x), i) == vec::get(v, i) by {
        apply(vec::get_push_kept(v, x, i));
    }
    ensures vec::len(vec::set(v, i, x)) == vec::len(v) by {
        apply(vec::len_set(v, i, x));
    }
    ensures vec::get(vec::set(v, i, x), i) == x by {
        apply(vec::get_set_same(v, i, x));
    }
    ensures vec::get(vec::set(v, i, x), j) == vec::get(v, j) by {
        apply(vec::get_set_other(v, i, j, x));
    }
    ensures v == w by {
        apply(vec::extensionality(v, w));
    }
}

theorem use_slice(p: uint8*, n: uint64) {
    ensures slice::len(slice::from_raw_parts(p, n)) == n by {
        unfold(slice::from_raw_parts(p, n));
        unfold(slice::len(Slice<uint8>::Slice(p, n)));
        normalize();
    }
    ensures slice::as_ptr(slice::from_raw_parts(p, n)) == p by {
        unfold(slice::from_raw_parts(p, n));
        unfold(slice::as_ptr(Slice<uint8>::Slice(p, n)));
        normalize();
    }
}
theorem restricted_view(A: Resource, B: Resource) {
    requires viewable(A);
    requires contains(A, B);
    ensures viewable(B) by {
        apply(separation::viewable_restrict(A, B)) using {
            viewable(A);
            contains(A, B);
        };
    }
}

theorem use_subslice_len(a: uint64, b: uint64, n: uint64) {
    requires a <= b;
    requires b <= n;
    ensures slice::subslice_len(a, b, n) == b - a by {
        solve();
    }
}

theorem check_integer_add_le(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a <= b;
    requires c <= d;
    ensures a + c <= b + d by {
        apply(integer::add_le(a, b, c, d)) using { a <= b; c <= d; };
    }
}

theorem check_integer_round_down_le(x: Integer) {
    requires x * 2 <= 5;
    ensures x <= 2 by {
        have (2 * 2) + 1 == 5 by { normalize(); }
        have x * 2 <= (2 * 2) + 1 by {
            rewrite((2 * 2) + 1, 5);
            known();
        }
        apply(integer::round_down_le(x, 2, 2, 1)) using {
            0 < 2; 1 < 2; x * 2 <= (2 * 2) + 1;
        };
    }
}


theorem check_integer_le_antisymmetric(a: Integer, b: Integer) {
    requires a <= b;
    requires b <= a;
    ensures a == b by {
        apply(integer::le_antisymmetric(a, b)) using { a <= b; b <= a; };
    }
}


theorem check_integer_le_substitute(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a <= b;
    requires c == a;
    requires d == b;
    ensures c <= d by {
        apply(integer::le_substitute(a, b, c, d)) using { a <= b; c == a; d == b; };
    }
}

theorem check_integer_equal_substitute(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a == b;
    requires c == a;
    requires d == b;
    ensures c == d by {
        apply(integer::equal_substitute(a, b, c, d)) using { a == b; c == a; d == b; };
    }
}

theorem check_integer_congruence(a: Integer, b: Integer, c: Integer, d: Integer, k: Integer) {
    requires a == b;
    requires c == d;
    ensures a + c == b + d by {
        apply(integer::equal_add(a, b, c, d)) using { a == b; c == d; };
    }
    ensures a * k == b * k by {
        apply(integer::equal_multiply(a, b, k)) using { a == b; };
    }
    ensures a - b == 0 by {
        apply(integer::equal_difference(a, b)) using { a == b; };
    }
    ensures a <= b by {
        apply(integer::equal_le(a, b)) using { a == b; };
    }
}

theorem check_integer_strict_step(a: Integer, b: Integer) {
    requires a < b;
    ensures a + 1 <= b by {
        apply(integer::lt_step_le(a,b)) using { a < b; };
    }
}
theorem check_integer_step_strict(a: Integer, b: Integer) {
    requires a + 1 <= b;
    ensures a < b by {
        apply(integer::step_le_lt(a,b)) using { a + 1 <= b; };
    }
}
theorem check_integer_disequal_strict(a: Integer, b: Integer) {
    requires a <= b;
    requires a != b;
    ensures a < b by {
        apply(integer::le_ne_lt(a,b)) using { a <= b; a != b; };
    }
}

theorem composition_differences(a: Integer, b: Integer) {
    requires a <= b;
    ensures a - b <= 0 by {
        apply(integer::le_difference(a, b, a - b)) using { a <= b; a - b == a - b; };
    }
    ensures a <= b by {
        have a - b <= 0 by {
            apply(integer::le_difference(a, b, a - b)) using { a <= b; a - b == a - b; };
        }
        apply(integer::difference_le(a, b, a - b)) using { a - b <= 0; a - b == a - b; };
    }
}

theorem check_integer_multiplication_equations(a: Integer, b: Integer) {
    ensures a * b == b * a by { apply(integer::multiply_commutative(a, b)); }
    ensures a * -b == -(a * b) by { apply(integer::multiply_negate(a, b)); }
}

theorem check_integer_order_composition(a: Integer, b: Integer, c: Integer) {
    requires a <= b;
    requires b <= c;
    ensures a <= c by {
        apply(integer::le_transitive(a, b, c)) using { a <= b; b <= c; };
    }
    ensures -b <= -a by {
        apply(integer::negate_order(a, b)) using { a <= b; };
    }
}

theorem check_integer_strict_weakening(a: Integer, b: Integer) {
    requires a < b;
    ensures a <= b by { apply(integer::lt_le(a, b)) using { a < b; }; }
}

theorem check_integer_product_interval(x: Integer, y: Integer) {
    requires -2 <= x;
    requires x <= 3;
    requires -4 <= y;
    requires y <= 5;
    ensures -12 <= x * y by {
        apply(integer::product_lower_bound(x, y, -2, 3, -4, 5, -12)) using {
            -2 <= x; x <= 3; -4 <= y; y <= 5;
            -12 <= (-2 * -4); -12 <= (-2 * 5);
            -12 <= (3 * -4); -12 <= (3 * 5);
        };
    }
    ensures x * y <= 15 by {
        apply(integer::product_upper_bound(x, y, -2, 3, -4, 5, 15)) using {
            -2 <= x; x <= 3; -4 <= y; y <= 5;
            (-2 * -4) <= 15; (-2 * 5) <= 15;
            (3 * -4) <= 15; (3 * 5) <= 15;
        };
    }
}


theorem check_add_right_order(a: Integer, b: Integer, c: Integer) {
    requires a <= b;
        ensures a + c <= b + c by {
        apply(integer::add_right_order(a, b, c)) using { a <= b; };
    }
}

theorem check_subtract_le(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a <= b;
    requires d <= c;
    ensures a - c <= b - d by {
        apply(integer::subtract_le(a, b, c, d)) using { a <= b; d <= c; };
    }
}

theorem check_subtract_right_order(a: Integer, b: Integer, c: Integer) {
    requires a <= b;
        ensures a - c <= b - c by {
        apply(integer::subtract_right_order(a, b, c)) using { a <= b; };
    }
}

theorem check_subtract_left_order(a: Integer, b: Integer, c: Integer) {
    requires a <= b;
        ensures c - b <= c - a by {
        apply(integer::subtract_left_order(a, b, c)) using { a <= b; };
    }
}

theorem check_negate_multiply(a: Integer, b: Integer) {
        ensures -a * b == -(a * b) by {
        apply(integer::negate_multiply(a, b));
    }
}

theorem check_equal_negate(a: Integer, b: Integer) {
    requires a == b;
        ensures -a == -b by {
        apply(integer::equal_negate(a, b)) using { a == b; };
    }
}

theorem check_sum_commute(a: Integer, b: Integer, c: Integer) {
    requires a == b + c;
        ensures a == c + b by {
        apply(integer::sum_commute(a, b, c)) using { a == b + c; };
    }
}

theorem check_sum_difference(a: Integer, b: Integer, c: Integer) {
    requires a == b + c;
        ensures a + -c == b by {
        apply(integer::sum_difference(a, b, c)) using { a == b + c; };
    }
    ensures -b == -a + c by {
        apply(integer::sum_difference(a, b, c)) using { a == b + c; };
    }
}

theorem check_positive_divisor_quotient_upper_rounded(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= n;
    requires n <= (bound * d) + (d - 1);
        ensures truncating_quotient(n, d) <= bound by {
        apply(integer::positive_divisor_quotient_upper_rounded(n, d, bound)) using { d != 0; 1 <= d; 0 <= n; n <= (bound * d) + (d - 1); };
    }
}

theorem check_positive_divisor_quotient_lower_rounded(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= 0;
    requires (bound * d) - (d - 1) <= n;
        ensures bound <= truncating_quotient(n, d) by {
        apply(integer::positive_divisor_quotient_lower_rounded(n, d, bound)) using { d != 0; 1 <= d; n <= 0; (bound * d) - (d - 1) <= n; };
    }
}

theorem check_nonnegative_dividend_remainder_upper(n: Integer, d: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= n;
        ensures truncating_remainder(n, d) <= n by {
        apply(integer::nonnegative_dividend_remainder_upper(n, d)) using { d != 0; 1 <= d; 0 <= n; };
    }
}

theorem check_nonpositive_dividend_remainder_lower(n: Integer, d: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= 0;
        ensures n <= truncating_remainder(n, d) by {
        apply(integer::nonpositive_dividend_remainder_lower(n, d)) using { d != 0; 1 <= d; n <= 0; };
    }
}

theorem check_quotient_upper_interval_nonnegative(n: Integer, d: Integer, numerator_bound: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= bound;
    requires endpoint <= d;
    requires n <= numerator_bound;
    requires numerator_bound <= bound * endpoint + (endpoint - 1);
        ensures truncating_quotient(n, d) <= bound by {
        apply(integer::quotient_upper_interval_nonnegative(n, d, numerator_bound, endpoint, bound)) using { d != 0; 1 <= d; 0 <= bound; endpoint <= d; n <= numerator_bound; numerator_bound <= bound * endpoint + (endpoint - 1); };
    }
}

theorem check_quotient_lower_interval_nonpositive(n: Integer, d: Integer, numerator_bound: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound <= 0;
    requires endpoint <= d;
    requires numerator_bound <= n;
    requires bound * endpoint - (endpoint - 1) <= numerator_bound;
        ensures bound <= truncating_quotient(n, d) by {
        apply(integer::quotient_lower_interval_nonpositive(n, d, numerator_bound, endpoint, bound)) using { d != 0; 1 <= d; bound <= 0; endpoint <= d; numerator_bound <= n; bound * endpoint - (endpoint - 1) <= numerator_bound; };
    }
}

theorem check_quotient_upper_interval_negative(n: Integer, d: Integer, numerator_bound: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound <= 0;
    requires d <= endpoint;
    requires n <= numerator_bound;
    requires numerator_bound <= bound * endpoint;
        ensures truncating_quotient(n, d) <= bound by {
        apply(integer::quotient_upper_interval_negative(n, d, numerator_bound, endpoint, bound)) using { d != 0; 1 <= d; bound <= 0; d <= endpoint; n <= numerator_bound; numerator_bound <= bound * endpoint; };
    }
}

theorem check_quotient_lower_interval_positive(n: Integer, d: Integer, numerator_bound: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= bound;
    requires d <= endpoint;
    requires numerator_bound <= n;
    requires bound * endpoint <= numerator_bound;
        ensures bound <= truncating_quotient(n, d) by {
        apply(integer::quotient_lower_interval_positive(n, d, numerator_bound, endpoint, bound)) using { d != 0; 1 <= d; 0 <= bound; d <= endpoint; numerator_bound <= n; bound * endpoint <= numerator_bound; };
    }
}

theorem check_remainder_lower_from_dividend(n: Integer, d: Integer, numerator_bound: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires numerator_bound <= n;
    requires bound <= numerator_bound;
    requires bound <= 0;
        ensures bound <= truncating_remainder(n, d) by {
        apply(integer::remainder_lower_from_dividend(n, d, numerator_bound, bound)) using { d != 0; 1 <= d; numerator_bound <= n; bound <= numerator_bound; bound <= 0; };
    }
}

theorem check_remainder_lower_from_divisor(n: Integer, d: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires d <= endpoint;
    requires bound <= 1 - endpoint;
        ensures bound <= truncating_remainder(n, d) by {
        apply(integer::remainder_lower_from_divisor(n, d, endpoint, bound)) using { d != 0; 1 <= d; d <= endpoint; bound <= 1 - endpoint; };
    }
}

theorem check_remainder_upper_from_dividend(n: Integer, d: Integer, numerator_bound: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= numerator_bound;
    requires numerator_bound <= bound;
    requires 0 <= bound;
        ensures truncating_remainder(n, d) <= bound by {
        apply(integer::remainder_upper_from_dividend(n, d, numerator_bound, bound)) using { d != 0; 1 <= d; n <= numerator_bound; numerator_bound <= bound; 0 <= bound; };
    }
}

theorem check_remainder_upper_from_divisor(n: Integer, d: Integer, endpoint: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires d <= endpoint;
    requires endpoint - 1 <= bound;
        ensures truncating_remainder(n, d) <= bound by {
        apply(integer::remainder_upper_from_divisor(n, d, endpoint, bound)) using { d != 0; 1 <= d; d <= endpoint; endpoint - 1 <= bound; };
    }
}

theorem check_small_remainder_interval(n: Integer, d: Integer, lo_n: Integer, hi_n: Integer, endpoint: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires endpoint <= d;
    requires lo_n <= n;
    requires n <= hi_n;
    requires 1 - endpoint <= lo_n;
    requires hi_n <= endpoint - 1;
        ensures truncating_remainder(n, d) == n by {
        apply(integer::small_remainder_interval(n, d, lo_n, hi_n, endpoint)) using { d != 0; 1 <= d; endpoint <= d; lo_n <= n; n <= hi_n; 1 - endpoint <= lo_n; hi_n <= endpoint - 1; };
    }
}

theorem check_nonzero_from_one(d: Integer) {
    requires 1 <= d;
    let one: Integer = 1;
        ensures d != 0 by {
        apply(integer::nonzero_from_one(d)) using { 1 <= d; };
    }
}

theorem check_nonzero_from_negative_one(d: Integer) {
    requires d <= -1;
    let zero: Integer = 0;
        ensures d != 0 by {
        apply(integer::nonzero_from_negative_one(d)) using { d <= -1; };
    }
}

theorem check_quotient_negate_divisor(n: Integer, d: Integer) {
    requires d != 0;
    requires -d != 0;
        ensures truncating_quotient(n, d) == -truncating_quotient(n, -d) by {
        apply(integer::quotient_negate_divisor(n, d)) using { d != 0; -d != 0; };
    }
}

theorem check_remainder_negate_divisor(n: Integer, d: Integer) {
    requires d != 0;
    requires -d != 0;
        ensures truncating_remainder(n, d) == truncating_remainder(n, -d) by {
        apply(integer::remainder_negate_divisor(n, d)) using { d != 0; -d != 0; };
    }
}


theorem use_multiply_associative(a:Integer,b:Integer,c:Integer) { ensures (a*b)*c==a*(b*c) by {apply(integer::multiply_associative(a,b,c));} }
theorem use_multiply_add_left(a:Integer,b:Integer,c:Integer) { ensures a*(b+c)==a*b+a*c by {apply(integer::multiply_add_left(a,b,c));} }
theorem use_negate_as_product(a:Integer) { ensures -a == -1*a by {apply(integer::negate_as_product(a));} }
theorem use_multiply_swap_front(a:Integer,b:Integer,c:Integer) { ensures a*(b*c)==b*(a*c) by {apply(integer::multiply_swap_front(a,b,c));} }
theorem use_nonnegative_quotient_from_remainder(n:Integer,d:Integer,q:Integer,r:Integer) {
 requires d!=0;requires 1<=d;requires 0<=n;requires 0<=r;requires r<=d-1;requires n==q*d+r;
 ensures truncating_quotient(n,d)==q by {apply(integer::nonnegative_quotient_from_remainder(n,d,q,r)) using {d!=0;1<=d;0<=n;0<=r;r<=d-1;n==q*d+r;};}
}
theorem use_nonnegative_quotient_shift(x:Integer,d:Integer,k:Integer) {
 requires d!=0;requires 1<=d;requires 0<=x;requires 0<=k;
 ensures truncating_quotient(x+d*k,d)==truncating_quotient(x,d)+k by {apply(integer::nonnegative_quotient_shift(x,d,k)) using {d!=0;1<=d;0<=x;0<=k;};}
}
theorem use_bytes_comparison_negative(left: uint8[], right: uint8[], length: uint64, first: uint64, cmp: int32) {
    requires bytes::comparison(left, right, length, cmp);
    requires first < length;
    requires bytes::equal_range(left, right, 0u64, first);
    requires left[first] < right[first];
    ensures cmp < 0 by apply(bytes::comparison_negative_after_prefix(left, right, length, first, cmp));
}

theorem use_bytes_comparison_positive(left: uint8[], right: uint8[], length: uint64, first: uint64, cmp: int32) {
    requires bytes::comparison(left, right, length, cmp);
    requires first < length;
    requires bytes::equal_range(left, right, 0u64, first);
    requires right[first] < left[first];
    ensures cmp > 0 by apply(bytes::comparison_positive_after_prefix(left, right, length, first, cmp));
}

theorem use_bytes_comparison_equal(left: uint8[], right: uint8[], length: uint64, cmp: int32) {
    requires bytes::comparison(left, right, length, cmp);
    requires bytes::equal(left, 0u64, right, 0u64, length);
    ensures cmp == 0 by apply(bytes::comparison_zero_when_equal(left, right, length, cmp));
}

```

```expect
pass
```
