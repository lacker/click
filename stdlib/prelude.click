function count(int32 p[], int32 lo, int32 hi, int32 x) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}

predicate permutation(int32 a[], int32 b[], int32 lo, int32 hi) {
    forall (int32 x) {
        count(a, lo, hi, x) == count(b, lo, hi, x)
    }
}

function byte_count(uint8 bytes[], int32 lo, int32 hi, uint8 value) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if bytes[k] == value { 1 } else { 0 }
    })
}

predicate bytes_equal(uint8 left[], int32 left_lo, uint8 right[], int32 right_lo, int32 len) {
    (0..len).all(|k| {
        left[left_lo + k] == right[right_lo + k]
    })
}

predicate bytes_equal_range(uint8 left[], uint8 right[], int32 lo, int32 hi) {
    (lo..hi).all(|k| {
        left[k] == right[k]
    })
}

predicate bytes_all_eq(uint8 bytes[], int32 lo, int32 hi, uint8 value) {
    (lo..hi).all(|k| {
        bytes[k] == value
    })
}

predicate bytes_contains(uint8 bytes[], int32 lo, int32 hi, uint8 value) {
    (lo..hi).any(|k| {
        bytes[k] == value
    })
}

predicate bytes_all_not_eq(uint8 bytes[], int32 lo, int32 hi, uint8 value) {
    (lo..hi).all(|k| {
        bytes[k] != value
    })
}

predicate cstr_prefix(uint8 bytes[], int32 len) {
    bytes_all_not_eq(bytes, 0, len, '\0')
}

predicate cstr_len(uint8 bytes[], int32 len) {
    0 <= len and cstr_prefix(bytes, len) and bytes_contains(bytes, len, len + 1, '\0')
}

predicate cstr(uint8 bytes[]) {
    exists (int32 len) {
        cstr_len(bytes, len)
    }
}

predicate cstr_bounded(uint8 bytes[], int32 max) {
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
