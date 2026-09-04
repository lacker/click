# `strlen` result can drive an explicitly framed byte read

The caller supplies an exact readable witness and retains a matching viewed
range. The C code then uses the length returned by `strlen` as an array index;
the view is the permission, while the readable-string fact supplies the
terminator value.

```c filename=cstr_dynamic_indexed_read.c
int32 read_terminator(uint8 bytes[], int32 known_len) {
    int32 length;
    length = strlen(bytes);
    return bytes[length];
}
```

```click
verifying "cstr_dynamic_indexed_read.c";

theorem cstr_readable_len_nonnegative(bytes: uint8[], len: int32) {
    requires cstr_readable_len(bytes, len);

    ensures 0 <= len by {
        unfold(cstr_readable_len);
        simp();
    }
}

int32 read_terminator(uint8 bytes[], int32 known_len) {
    requires cstr_readable(bytes);
    requires cstr_readable_len(bytes, known_len);
    requires 0 <= known_len;
    requires known_len < 2147483647;
    requires loadable(bytes[0..known_len + 1]);
    requires forall (k: int32) {
        0 <= k and k < known_len implies bytes[k] != '\0'
    };
    requires bytes[known_len] == '\0';
    views bytes[0..known_len + 1];
    ensures result == '\0' by {
        unfold(cstr_readable);
        unfold(cstr_readable_len);
        execute_until(statement(2));
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
        execute();
        simp();
    }
}
```

```expect
pass
```
