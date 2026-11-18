# Readable bytes and a length witness do not supply a held C string

The caller owns the raw bytes and has pure facts about the string and its
length. After declaring the local, the proof observes the byte range directly
and constructs the readable witness. The intervening self-assignment leaves
the caller without the `cstr_at` resource that `strlen` requires.

```c filename=cstr_dynamic_invalidated_transport.c
uint64 read_terminator(uint8 bytes[], uint64 known_len) {
    uint64 length;
    bytes[0] = bytes[0];
    length = strlen(bytes);
    return length;
}
```

```click
verifying "cstr_dynamic_invalidated_transport.c";

uint64 read_terminator(uint8 bytes[], uint64 known_len) {
    requires click::c::string::readable(bytes);
    requires click::c::string::readable_len(bytes, known_len);
    requires known_len < 18446744073709551615u64;
    requires viewable(bytes[0..known_len + 1u64]);
    owns bytes[0..known_len + 1u64];
    ensures result < 18446744073709551615u64;
} by {
    unfold(click::c::string::readable_len(bytes, known_len));
    step();
    have forall (k: uint64) {
        to_integer(k) < to_integer(known_len) + 1 implies defined(bytes[k])
    } by {
        intro(); intro();
        have to_integer(k) < to_integer(known_len + 1u64) by {
            solve() using {
                to_integer(k) < to_integer(known_len) + 1;
                known_len < 18446744073709551615u64;
            };
        }
        have 0u64 <= k by { normalize(); }
        instantiate(forall (j: uint64) {
            0u64 <= j and to_integer(j) < to_integer(known_len + 1u64) implies defined(old(bytes[j]))
        }, k);
        have defined(old(bytes[k])) by { known(); }
        have separate(memory(length), memory(bytes[k])) by { normalize(); }
        have separate(statement(0).footprint, memory(bytes[k])) by {
            normalize() using { separate(memory(length), memory(bytes[k])); };
        }
        preserve(memory(bytes[k]), statement(0));
    }
    observe(bytes[0..known_len + 1u64]);
    have exists (len: uint64) {
        len < 18446744073709551615u64 and
            viewable(bytes[0..len + 1u64]) and
            forall (k: uint64) { k < len implies bytes[k] != '\0' } and
            bytes[len] == '\0' and
            forall (k: uint64) { to_integer(k) < to_integer(len) + 1 implies defined(bytes[k]) }
    } by {
        witness(known_len);
        known();
    }
    step();
    step();
}
```

```expect
fail: call to `strlen` needs a held `cstr_at` instance to give `n` its value
```
