import click::bytes;

// C strings, measured as C measures them: a length is a `size_t`. A string
// of length `len` occupies `len + 1` bytes, so `len` is below `SIZE_MAX`,
// which also keeps `len + 1` exact.
predicate prefix(bytes: uint8[], len: uint64) {
    forall (k: uint64) { k < len implies bytes[k] != '\0' }
}

predicate len(bytes: uint8[], len: uint64) {
    len < 18446744073709551615u64 and
        viewable(bytes[0..len + 1u64]) and
        string::prefix(bytes, len) and
        bytes[len] == '\0'
}

predicate cstr(bytes: uint8[]) {
    exists (len: uint64) {
        string::len(bytes, len)
    }
}

predicate readable_len(bytes: uint8[], len: uint64) {
    len < 18446744073709551615u64 and
        viewable(bytes[0..len + 1u64]) and
        forall (k: uint64) { k < len implies bytes[k] != '\0' } and
        bytes[len] == '\0' and
        forall (k: uint64) { to_integer(k) < to_integer(len + 1u64) implies defined(bytes[k]) }
}

theorem readable_len_unique(bytes: uint8[], left: uint64, right: uint64) {
    requires forall (k: uint64) { k < left implies bytes[k] != '\0' };
    requires bytes[left] == '\0';
    requires forall (k: uint64) { k < right implies bytes[k] != '\0' };
    requires bytes[right] == '\0';

    ensures left == right by {
        have left < right or not (left < right) by {
            if left < right {
                known();
            } else {
                known();
            }
        }
        cases {
            left < right => {
                instantiate(forall (k: uint64) { k < right implies bytes[k] != '\0' }, left);
                contradiction(false);
            }
            not (left < right) => {
                have right < left or not (right < left) by {
                    if right < left {
                        known();
                    } else {
                        known();
                    }
                }
                cases {
                    right < left => {
                        instantiate(forall (k: uint64) { k < left implies bytes[k] != '\0' }, right);
                        contradiction(false);
                    }
                    not (right < left) => {
                        have left <= right by {
                            solve();
                        }
                        solve();
                    }
                }
            }
        }
    }
}

predicate readable(bytes: uint8[]) {
    exists (len: uint64) {
        len < 18446744073709551615u64 and
            viewable(bytes[0..len + 1u64]) and
            forall (k: uint64) { k < len implies bytes[k] != '\0' } and
            bytes[len] == '\0' and
            forall (k: uint64) { to_integer(k) < to_integer(len + 1u64) implies defined(bytes[k]) }
    }
}

// A C string: the bytes of `p` through its first terminator, with the facts
// that make them the C string of length `len`. The body owns the bytes; a
// contract chooses how it holds them: `views` borrows the string read-only,
// `owns` returns the same instance (so the same length), and `consumes` with
// `produces` changes it.
resource cstr_at(p: const uint8*, len: uint64) {
    owns p[0..len + 1u64];
    fact len < 18446744073709551615u64;
    fact forall (k: uint64) { 0u64 <= k and k < len implies p[k] != '\0' };
    fact p[len] == '\0';
    fact forall (k: uint64) { 0u64 <= k and to_integer(k) < to_integer(len + 1u64) implies defined(p[k]) };
}

predicate bounded(bytes: uint8[], max: uint64) {
    exists (k: uint64) { k < max and bytes[k] == '\0' }
}

theorem len_is_viewable(bytes: uint8[], len: uint64) {
    requires string::len(bytes, len);

    ensures viewable(bytes[0..len + 1u64]) by {
        unfold(string::len(bytes, len));
        solve();
    }
}

theorem len_has_prefix(bytes: uint8[], len: uint64) {
    requires string::len(bytes, len);

    ensures string::prefix(bytes, len) by {
        unfold(string::len(bytes, len));
        solve();
    }
}

theorem len_has_terminator(bytes: uint8[], len: uint64) {
    requires string::len(bytes, len);

    ensures bytes[len] == '\0' by {
        unfold(string::len(bytes, len));
        solve();
    }
}

// The C library's byte functions, with C's `size_t` counts. memset converts
// its int fill value to unsigned char, reducing it modulo 256.
extern uint8* memcpy(uint8 destination[], const uint8 source[], uint64 bytes) {
    views source[0..bytes];
    owns uninitialized(destination[0..bytes]);
    ensures result == destination;
    ensures bytes::equal(destination, 0u64, old(source), 0u64, bytes);
}

extern int32 memcmp(const uint8 left[], const uint8 right[], uint64 bytes) {
    views left[0..bytes];
    views right[0..bytes];
    requires forall (k: uint64) { k < bytes implies defined(left[k]) and defined(right[k]) };
    ensures bytes::comparison(left, right, bytes, result);
}

extern uint8* memset(uint8 destination[], int32 value, uint64 bytes) {
    owns uninitialized(destination[0..bytes]);
    ensures result == destination;
    ensures (0u64..bytes).all(|k| {
        defined(destination[k]) and destination[k] == (value as uint8)
    });
}

extern uint64 strlen(const uint8* bytes) {
    let n: uint64;
    views cstr_at(bytes, n);
    ensures result == n;
}
