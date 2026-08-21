# Standard library

The Click standard library is the public Surface Click API loaded from
`stdlib/prelude.click` with every user sidecar. It isn't the Rust crate's
internal `pub` API.

Every declaration below is copied exactly from the prelude and checked by the
documentation gate. The same gate compares declaration names bidirectionally,
so adding, removing, or changing a public symbol requires a matching reference
update.

Pure functions are definitionally expanded when Click lowers a call. Predicates
remain opaque until a proof explicitly unfolds them or applies a theorem that
exposes the needed consequence. Theorems can be applied when their stated
requirements are available. An abstract resource has no body to unfold.

## Allocation authority

### `allocation`

```click
abstract resource allocation(base: int32*, bytes: int32);
```

**Meaning:** Owns the lifetime authority for the heap allocation whose base pointer is `base` and whose extent is `bytes`. The resource is abstract and cannot be unfolded.

**Kind:** abstract resource. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

## Signed `int32` theorems

### `int32_increment_upper_bound`

```click
theorem int32_increment_upper_bound(value: int32, upper: int32) {
    requires value < upper;

    ensures value + 1 <= upper;
}
```

**Meaning:** Given its listed requirements, proves `value + 1 <= upper`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_increment_strictly_increases`

```click
theorem int32_increment_strictly_increases(value: int32, upper: int32) {
    requires value < upper;

    ensures value < value + 1;
}
```

**Meaning:** Given its listed requirements, proves `value < value + 1`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_increment_lower_bound`

```click
theorem int32_increment_lower_bound(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures lower <= value + 1;
}
```

**Meaning:** Given its listed requirements, proves `lower <= value + 1`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_increment_greater_equal_lower_bound`

```click
theorem int32_increment_greater_equal_lower_bound(value: int32, lower: int32, upper: int32) {
    requires value >= lower;
    requires value < upper;

    ensures value + 1 >= lower;
}
```

**Meaning:** Given its listed requirements, proves `value + 1 >= lower`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_increment_strict_greater_lower_bound`

```click
theorem int32_increment_strict_greater_lower_bound(value: int32, lower: int32, upper: int32) {
    requires value >= lower;
    requires value < upper;

    ensures value + 1 > lower;
}
```

**Meaning:** Given its listed requirements, proves `value + 1 > lower`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_increment_preserves_order`

```click
theorem int32_increment_preserves_order(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures lower + 1 <= value + 1;
}
```

**Meaning:** Given its listed requirements, proves `lower + 1 <= value + 1`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_successor_le_implies_lt`

```click
theorem int32_successor_le_implies_lt(lower: int32, value: int32) {
    requires lower < lower + 1;
    requires lower + 1 <= value;

    ensures lower < value;
}
```

**Meaning:** Given its listed requirements, proves `lower < value`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_positive_is_nonnegative`

```click
theorem int32_positive_is_nonnegative(value: int32) {
    requires 1 <= value;

    ensures 0 <= value;
}
```

**Meaning:** Given its listed requirements, proves `0 <= value`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_lt_implies_le`

```click
theorem int32_lt_implies_le(left: int32, right: int32) {
    requires left < right;

    ensures left <= right;
}
```

**Meaning:** Given its listed requirements, proves `left <= right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_not_lt_implies_ge`

```click
theorem int32_not_lt_implies_ge(left: int32, right: int32) {
    requires not (left < right);

    ensures left >= right;
}
```

**Meaning:** Given its listed requirements, proves `left >= right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_strictly_positive_is_nonnegative`

```click
theorem int32_strictly_positive_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures value >= 0;
}
```

**Meaning:** Given its listed requirements, proves `value >= 0`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_increment_below_max_is_defined`

```click
theorem int32_increment_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(value + 1);
}
```

**Meaning:** Given its listed requirements, proves `defined(value + 1)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_one_plus_below_max_is_defined`

```click
theorem int32_one_plus_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(1 + value);
}
```

**Meaning:** Given its listed requirements, proves `defined(1 + value)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_one_plus_strictly_increases`

```click
theorem int32_one_plus_strictly_increases(value: int32) {
    requires value < 2147483647;

    ensures value < 1 + value;
}
```

**Meaning:** Given its listed requirements, proves `value < 1 + value`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_nonnegative_add_within_max_is_defined`

```click
theorem int32_nonnegative_add_within_max_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires value <= 2147483647 - amount;

    ensures defined(value + amount);
}
```

**Meaning:** Given its listed requirements, proves `defined(value + amount)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_nonnegative_subtract_within_value_is_defined`

```click
theorem int32_nonnegative_subtract_within_value_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires amount <= value;

    ensures defined(value - amount);
}
```

**Meaning:** Given its listed requirements, proves `defined(value - amount)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_move_one_from_right_to_left_preserves_sum`

```click
theorem int32_move_one_from_right_to_left_preserves_sum(
    total: int32,
    left: int32,
    right: int32
) {
    requires 0 <= left;
    requires 1 <= right;
    requires total == left + right;

    ensures total == (left + 1) + (right - 1);
}
```

**Meaning:** Given its listed requirements, proves `total == (left + 1) + (right - 1)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_subtract_equal_sum_right_cancels`

```click
theorem int32_subtract_equal_sum_right_cancels(value: int32, left: int32, amount: int32) {
    requires defined(left + amount) and value == left + amount;
    requires defined(value - amount);

    ensures value - amount == left by {
        rewrite(value == left + amount);
        simp();
    }
}
```

**Meaning:** Given its listed requirements, proves `value - amount == left`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_add_nonnegative_right_is_at_least_left`

```click
theorem int32_add_nonnegative_right_is_at_least_left(left: int32, right: int32) {
    requires 0 <= right;
    requires defined(left + right);

    ensures left <= left + right;
}
```

**Meaning:** Given its listed requirements, proves `left <= left + right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_add_nonnegative_left_is_at_least_right`

```click
theorem int32_add_nonnegative_left_is_at_least_right(left: int32, right: int32) {
    requires 0 <= left;
    requires defined(left + right);

    ensures right <= left + right;
}
```

**Meaning:** Given its listed requirements, proves `right <= left + right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_positive_predecessor_is_nonnegative`

```click
theorem int32_positive_predecessor_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value - 1;
}
```

**Meaning:** Given its listed requirements, proves `0 <= value - 1`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_above_one_predecessor_is_at_least_one`

```click
theorem int32_above_one_predecessor_is_at_least_one(value: int32) {
    requires 1 < value;

    ensures value - 1 >= 1;
}
```

**Meaning:** Given its listed requirements, proves `value - 1 >= 1`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_positive_predecessor_strictly_decreases`

```click
theorem int32_positive_predecessor_strictly_decreases(value: int32) {
    requires 0 < value;

    ensures value - 1 < value;
}
```

**Meaning:** Given its listed requirements, proves `value - 1 < value`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_nonnegative_predecessor_upper_bound`

```click
theorem int32_nonnegative_predecessor_upper_bound(value: int32, bound: int32) {
    requires 0 <= value;
    requires value <= bound;

    ensures value - 1 <= bound;
}
```

**Meaning:** Given its listed requirements, proves `value - 1 <= bound`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_le_lt_transitive`

```click
theorem int32_le_lt_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last;
}
```

**Meaning:** Given its listed requirements, proves `first < last`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_le_transitive`

```click
theorem int32_le_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last;
}
```

**Meaning:** Given its listed requirements, proves `first <= last`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_lt_transitive`

```click
theorem int32_lt_transitive(first: int32, middle: int32, last: int32) {
    requires first < middle;
    requires middle < last;

    ensures first < last;
}
```

**Meaning:** Given its listed requirements, proves `first < last`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_lt_le_transitive`

```click
theorem int32_lt_le_transitive(first: int32, middle: int32, last: int32) {
    requires first < middle;
    requires middle <= last;

    ensures first < last;
}
```

**Meaning:** Given its listed requirements, proves `first < last`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_ge_transitive`

```click
theorem int32_ge_transitive(last: int32, middle: int32, first: int32) {
    requires last >= middle;
    requires middle >= first;

    ensures last >= first;
}
```

**Meaning:** Given its listed requirements, proves `last >= first`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_ge_implies_reversed_le`

```click
theorem int32_ge_implies_reversed_le(greater: int32, lower: int32) {
    requires greater >= lower;

    ensures lower <= greater;
}
```

**Meaning:** Given its listed requirements, proves `lower <= greater`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_le_implies_reversed_ge`

```click
theorem int32_le_implies_reversed_ge(lower: int32, greater: int32) {
    requires lower <= greater;

    ensures greater >= lower;
}
```

**Meaning:** Given its listed requirements, proves `greater >= lower`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_le_and_not_lt_implies_eq`

```click
theorem int32_le_and_not_lt_implies_eq(left: int32, right: int32) {
    requires left <= right;
    requires not (left < right);

    ensures left == right;
}
```

**Meaning:** Given its listed requirements, proves `left == right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_le_and_neq_implies_lt`

```click
theorem int32_le_and_neq_implies_lt(left: int32, right: int32) {
    requires left <= right;
    requires left != right;

    ensures left < right;
}
```

**Meaning:** Given its listed requirements, proves `left < right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `int32_ge_and_not_gt_implies_eq`

```click
theorem int32_ge_and_not_gt_implies_eq(left: int32, right: int32) {
    requires left >= right;
    requires not (left > right);

    ensures left == right;
}
```

**Meaning:** Given its listed requirements, proves `left == right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

## Array specifications

### `count`

```click
function count(p: int32[], lo: int32, hi: int32, x: int32) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}
```

**Meaning:** Returns the number of elements equal to `x` in the half-open range `lo..hi` of the `int32` array reference `p`.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `permutation`

```click
predicate permutation(a: int32[], b: int32[], lo: int32, hi: int32) {
    forall (x: int32) {
        count(a, lo, hi, x) == count(b, lo, hi, x)
    }
}
```

**Meaning:** States that `a` and `b` contain every `int32` value the same number of times in `lo..hi`. Unfolding exposes equality of two `count` calls under a universal quantifier.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(permutation)` when a proof needs the predicate body.

## Byte-range specifications

### `byte_count`

```click
function byte_count(bytes: uint8[], lo: int32, hi: int32, value: uint8) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if bytes[k] == value { 1 } else { 0 }
    })
}
```

**Meaning:** Returns the number of bytes equal to `value` in the half-open range `lo..hi`.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `bytes_equal`

```click
predicate bytes_equal(left: uint8[], left_lo: int32, right: uint8[], right_lo: int32, len: int32) {
    (0..len).all(|k| {
        left[left_lo + k] == right[right_lo + k]
    })
}
```

**Meaning:** States that the `len` bytes starting at `left_lo` and `right_lo` are pairwise equal.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes_equal)` when a proof needs the predicate body.

### `bytes_equal_range`

```click
predicate bytes_equal_range(left: uint8[], right: uint8[], lo: int32, hi: int32) {
    (lo..hi).all(|k| {
        left[k] == right[k]
    })
}
```

**Meaning:** States that `left` and `right` are pairwise equal throughout the same half-open range `lo..hi`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes_equal_range)` when a proof needs the predicate body.

### `bytes_all_eq`

```click
predicate bytes_all_eq(bytes: uint8[], lo: int32, hi: int32, value: uint8) {
    (lo..hi).all(|k| {
        bytes[k] == value
    })
}
```

**Meaning:** States that every byte in `lo..hi` equals `value`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes_all_eq)` when a proof needs the predicate body.

### `bytes_contains`

```click
predicate bytes_contains(bytes: uint8[], lo: int32, hi: int32, value: uint8) {
    (lo..hi).any(|k| {
        bytes[k] == value
    })
}
```

**Meaning:** States that at least one byte in `lo..hi` equals `value`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes_contains)` when a proof needs the predicate body.

### `bytes_all_not_eq`

```click
predicate bytes_all_not_eq(bytes: uint8[], lo: int32, hi: int32, value: uint8) {
    (lo..hi).all(|k| {
        bytes[k] != value
    })
}
```

**Meaning:** States that every byte in `lo..hi` differs from `value`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes_all_not_eq)` when a proof needs the predicate body.

## C-string specifications

### `cstr_prefix`

```click
predicate cstr_prefix(bytes: uint8[], len: int32) {
    bytes_all_not_eq(bytes, 0, len, '\0')
}
```

**Meaning:** States that the first `len` bytes contain no null terminator.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(cstr_prefix)` when a proof needs the predicate body.

### `cstr_len`

```click
predicate cstr_len(bytes: uint8[], len: int32) {
    0 <= len and cstr_prefix(bytes, len) and bytes_contains(bytes, len, len + 1, '\0')
}
```

**Meaning:** States that `len` is nonnegative, the preceding bytes contain no null terminator, and byte `len` is a null terminator.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(cstr_len)` when a proof needs the predicate body.

### `cstr`

```click
predicate cstr(bytes: uint8[]) {
    exists (len: int32) {
        cstr_len(bytes, len)
    }
}
```

**Meaning:** States that the byte array has some exact specification-level C-string length.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(cstr)` when a proof needs the predicate body.

### `cstr_bounded`

```click
predicate cstr_bounded(bytes: uint8[], max: int32) {
    bytes_contains(bytes, 0, max, '\0')
}
```

**Meaning:** States that a null terminator occurs before the exclusive bound `max`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(cstr_bounded)` when a proof needs the predicate body.

### `cstr_len_nonnegative`

```click
theorem cstr_len_nonnegative(bytes: uint8[], len: int32) {
    requires cstr_len(bytes, len);

    ensures 0 <= len by {
        unfold(cstr_len);
        simp();
    }
}
```

**Meaning:** Given its listed requirements, proves `0 <= len`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `cstr_len_has_prefix`

```click
theorem cstr_len_has_prefix(bytes: uint8[], len: int32) {
    requires cstr_len(bytes, len);

    ensures cstr_prefix(bytes, len) by {
        unfold(cstr_len);
        simp();
    }
}
```

**Meaning:** Given its listed requirements, proves `cstr_prefix(bytes, len)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `cstr_len_has_terminator`

```click
theorem cstr_len_has_terminator(bytes: uint8[], len: int32) {
    requires cstr_len(bytes, len);

    ensures bytes_contains(bytes, len, len + 1, '\0') by {
        unfold(cstr_len);
        simp();
    }
}
```

**Meaning:** Given its listed requirements, proves `bytes_contains(bytes, len, len + 1, '\0')`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/lacker/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

## Namespace and extension rules

Standard-library definitions share the logic-declaration namespace with user
Click definitions. A user predicate, pure function, resource, or theorem can't
redefine a prelude name. A C function contract can have the same name as a
prelude pure function when no user Click definition creates a conflict.

To add a public symbol:

1. Add its declaration to `stdlib/prelude.click`.
2. Add a focused mdtest that uses it from an ordinary sidecar.
3. Add its semantic entry here; the inventory and exact-declaration checks fail
   until this page agrees with the source.
4. Add general prover or kernel support only when the definition exposes a
   reusable reasoning gap. Don't hard-code a domain-specific library name into
   the kernel merely because it is useful.
