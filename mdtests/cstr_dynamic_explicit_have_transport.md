# Explicitly prove `strlen`'s dynamic readable witness across a local declaration

```c filename=cstr_dynamic_explicit_have_transport.c
int32 read_terminator(uint8 bytes[], uint64 known_len) {
    uint64 length;
    length = strlen(bytes);
    return bytes[length];
}
```

```click
verifying "cstr_dynamic_explicit_have_transport.c";

int32 read_terminator(uint8 bytes[], uint64 known_len) {
    requires cstr_readable(bytes);
    requires cstr_readable_len(bytes, known_len);
    requires known_len < 18446744073709551615u64;
    requires viewable(bytes[0..known_len + 1u64]);
    views bytes[0..known_len + 1u64];
    ensures result == '\0' by {
        unfold(cstr_readable);
        unfold(cstr_readable_len);
        execute_until(statement(1));
        have viewable(bytes[0..known_len + 1u64]) by {
            transport(
                at(function.entry, viewable(bytes[0..known_len + 1u64])),
                viewable(bytes[0..known_len + 1u64])
            ) using { at(function.entry, viewable(bytes[0..known_len + 1u64])); }
        }
        have forall (k: uint64) { k < known_len + 1u64 implies defined(bytes[k]) } by {
            extract(at(function.entry, forall (k: uint64) {
                k < known_len + 1u64 implies defined(bytes[k])
            }));
            intro();
            intro();
            instantiate(at(function.entry, forall (k: uint64) {
                k < known_len + 1u64 implies defined(bytes[k])
            }), k) using {
                k < known_len + 1u64;
            }
            transport(
                at(function.entry, defined(bytes[k])),
                defined(bytes[k])
            ) using { at(function.entry, defined(bytes[k])); }
        }
        have forall (k: uint64) { k < known_len implies bytes[k] != '\0' } by {
            extract(at(function.entry, forall (k: uint64) {
                k < known_len implies bytes[k] != '\0'
            }));
        }
        have exists (len: uint64) {
            len < 18446744073709551615u64 and viewable(bytes[0..len + 1u64]) and
            forall (k: uint64) { k < len implies bytes[k] != '\0' } and
            bytes[len] == '\0' and
            forall (k: uint64) { k < len + 1u64 implies defined(bytes[k]) }
        } by {
            witness { len: known_len };
            simp();
        }
        step();
        unfold(cstr_readable_len);
        apply(cstr_readable_len_unique(
            bytes,
            at(statement(2).entry, c(length)),
            known_len
        )) using {
            forall (k: uint64) {
                k < at(statement(2).entry, c(length)) implies bytes[k] != '\0'
            };
            bytes[at(statement(2).entry, c(length))] == '\0';
            forall (k: uint64) { k < known_len implies bytes[k] != '\0' };
            bytes[known_len] == '\0';
        }
        step();
        simp();
    }
}
```

```expect
pass
```
