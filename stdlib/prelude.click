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
