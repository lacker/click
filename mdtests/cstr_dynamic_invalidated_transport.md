# An intervening write invalidates a dynamic viewability transport

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
    requires cstr_readable(bytes);
    requires cstr_readable_len(bytes, known_len);
    requires known_len < 18446744073709551615u64;
    requires viewable(bytes[0..known_len + 1u64]);
    owns bytes[0..known_len + 1u64];
    ensures result < 18446744073709551615u64 by {
        unfold(cstr_readable);
        unfold(cstr_readable_len);
        step();
        have exists (len: uint64) {
            len < 18446744073709551615u64 and
                viewable(bytes[0..len + 1u64]) and
                forall (k: uint64) { k < len implies bytes[k] != '\0' } and
                bytes[len] == '\0' and
                forall (k: uint64) { k < len + 1u64 implies defined(bytes[k]) }
        } by {
            witness { len: known_len }
            both {
                both {
                    both {
                        both {
                            simp();
                        } and {
                            transport(
                                at(function.entry, viewable(bytes[0..known_len + 1u64])),
                                viewable(bytes[0..known_len + 1u64])
                            ) using {
                                at(function.entry, viewable(bytes[0..known_len + 1u64]));
                            }
                        }
                    } and {
                        simp();
                    }
                } and {
                    simp();
                }
            } and {
                simp();
            }
        }
    }
}
```

```expect
fail: missing prerequisite (precondition clause 1 of `strlen`)
```
