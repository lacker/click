resource allocation(base: int32*, bytes: int32);

theorem int32_increment_upper_bound(value: int32, upper: int32) {
    requires value < upper;

    ensures value + 1 <= upper;
}

theorem int32_increment_strictly_increases(value: int32, upper: int32) {
    requires value < upper;

    ensures value < value + 1;
}

theorem int32_increment_lower_bound(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures lower <= value + 1;
}

theorem int32_increment_preserves_order(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures lower + 1 <= value + 1;
}

theorem int32_successor_le_implies_lt(lower: int32, value: int32) {
    requires lower < lower + 1;
    requires lower + 1 <= value;

    ensures lower < value;
}

theorem int32_positive_is_nonnegative(value: int32) {
    requires 1 <= value;

    ensures 0 <= value;
}

theorem int32_positive_predecessor_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value - 1;
}

theorem int32_positive_predecessor_strictly_decreases(value: int32) {
    requires 0 < value;

    ensures value - 1 < value;
}

theorem int32_le_lt_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last;
}

theorem int32_le_and_not_lt_implies_eq(left: int32, right: int32) {
    requires left <= right;
    requires not (left < right);

    ensures left == right;
}

function count(p: int32[], lo: int32, hi: int32, x: int32) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}

predicate permutation(a: int32[], b: int32[], lo: int32, hi: int32) {
    forall (x: int32) {
        count(a, lo, hi, x) == count(b, lo, hi, x)
    }
}

function byte_count(bytes: uint8[], lo: int32, hi: int32, value: uint8) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if bytes[k] == value { 1 } else { 0 }
    })
}

predicate bytes_equal(left: uint8[], left_lo: int32, right: uint8[], right_lo: int32, len: int32) {
    (0..len).all(|k| {
        left[left_lo + k] == right[right_lo + k]
    })
}

predicate bytes_equal_range(left: uint8[], right: uint8[], lo: int32, hi: int32) {
    (lo..hi).all(|k| {
        left[k] == right[k]
    })
}

predicate bytes_all_eq(bytes: uint8[], lo: int32, hi: int32, value: uint8) {
    (lo..hi).all(|k| {
        bytes[k] == value
    })
}

predicate bytes_contains(bytes: uint8[], lo: int32, hi: int32, value: uint8) {
    (lo..hi).any(|k| {
        bytes[k] == value
    })
}

predicate bytes_all_not_eq(bytes: uint8[], lo: int32, hi: int32, value: uint8) {
    (lo..hi).all(|k| {
        bytes[k] != value
    })
}

predicate cstr_prefix(bytes: uint8[], len: int32) {
    bytes_all_not_eq(bytes, 0, len, '\0')
}

predicate cstr_len(bytes: uint8[], len: int32) {
    0 <= len and cstr_prefix(bytes, len) and bytes_contains(bytes, len, len + 1, '\0')
}

predicate cstr(bytes: uint8[]) {
    exists (len: int32) {
        cstr_len(bytes, len)
    }
}

predicate cstr_bounded(bytes: uint8[], max: int32) {
    bytes_contains(bytes, 0, max, '\0')
}

theorem cstr_len_nonnegative(bytes: uint8[], len: int32) {
    requires cstr_len(bytes, len);

    ensures 0 <= len by {
        unfold(cstr_len);
        simp();
    }
}

theorem cstr_len_has_prefix(bytes: uint8[], len: int32) {
    requires cstr_len(bytes, len);

    ensures cstr_prefix(bytes, len) by {
        unfold(cstr_len);
        simp();
    }
}

theorem cstr_len_has_terminator(bytes: uint8[], len: int32) {
    requires cstr_len(bytes, len);

    ensures bytes_contains(bytes, len, len + 1, '\0') by {
        unfold(cstr_len);
        simp();
    }
}
