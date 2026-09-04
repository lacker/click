# Dynamically loadable C-string witness for `strlen`

```c filename=cstr_dynamic_loadability.c
int32 read_terminator(uint8 bytes[]) {
    int32 length;
    length = strlen(bytes);
    return length;
}
```

```click
verifying "cstr_dynamic_loadability.c";

int32 read_terminator(uint8 bytes[]) {
    requires input: cstr_readable(bytes);
    ensures result >= 0;
} by {
    unfold(cstr_readable);
    execute();
    simp();
}
```

```expect
pass
```
