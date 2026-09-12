# Dynamic range transport is required across a local declaration

```c filename=cstr_dynamic_transport_required.c
int32 read_terminator(uint8 bytes[], int32 known_len) {
    int32 length;
    length = strlen(bytes);
    return length;
}
```

```click
verifying "cstr_dynamic_transport_required.c";

int32 read_terminator(uint8 bytes[], int32 known_len) {
    requires input: cstr_readable(bytes);
    requires input_len: cstr_readable_len(bytes, known_len);
    requires 0 <= known_len;
    requires known_len < 2147483647;
    requires loadable(bytes[0..known_len + 1]);
    ensures result >= 0 by {
        unfold(cstr_readable);
        unfold(cstr_readable_len);
        execute_until(statement(1));
        have loadable(bytes[0..known_len + 1]) by {
            assumption();
        }
    }
}
```

```expect
fail: assumption` requires the current goal as an available semantic fact
```
