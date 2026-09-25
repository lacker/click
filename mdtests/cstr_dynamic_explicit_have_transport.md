# Explicitly prove `strlen`'s dynamic readable witness across a local declaration

```c filename=cstr_dynamic_explicit_have_transport.c
int32 read_terminator(uint8 bytes[], int32 known_len) {
    int32 length;
    length = strlen(bytes);
    return bytes[length];
}
```

```click
verifying "cstr_dynamic_explicit_have_transport.c";

int32 read_terminator(uint8 bytes[], int32 known_len) {
    requires cstr_readable(bytes);
    requires cstr_readable_len(bytes, known_len);
    requires 0 <= known_len;
    requires known_len < 2147483647;
    requires viewable(bytes[0..known_len + 1]);
    views bytes[0..known_len + 1];
    ensures result == '\0' by {
        unfold(cstr_readable);
        unfold(cstr_readable_len);
        execute_until(statement(1));
        have viewable(bytes[0..known_len + 1]) by {
            transport(
                at(function.entry, viewable(bytes[0..known_len + 1])),
                viewable(bytes[0..known_len + 1])
            ) using { at(function.entry, viewable(bytes[0..known_len + 1])); }
        }
        have exists (len: int32) {
            0 <= len and viewable(bytes[0..len + 1]) and
            forall (k: int32) { 0 <= k and k < len implies bytes[k] != '\0' } and
            bytes[len] == '\0' and
            forall (k: int32) { 0 <= k and k < len + 1 implies defined(bytes[k]) }
        } by {
            witness(len = known_len);
            simp();
        }
        step();
        unfold(cstr_readable_len);
        apply(cstr_readable_len_unique(
            bytes,
            at(statement(2).entry, c(length)),
            known_len
        )) using {
            at(statement(2).entry, c(length)) >= 0;
            forall (k: int32) {
                0 <= k and k < at(statement(2).entry, c(length)) implies bytes[k] != '\0'
            };
            bytes[at(statement(2).entry, c(length))] == '\0';
            0 <= known_len;
            forall (k: int32) {
                0 <= k and k < known_len implies bytes[k] != '\0'
            };
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
