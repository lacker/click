# A caller's C-string requirement does not reach a copy that points elsewhere

`p = bytes + 1` is not the pointer the caller's `cstr_readable(bytes)` names,
so `strlen(p)`'s precondition is still missing.

```c filename=cstr_offset_copy.c
uint64 offset(uint8 bytes[]) {
    uint8* p;
    p = bytes + 1;
    return strlen(p);
}
```

```click
verifying "cstr_offset_copy.c";

uint64 offset(uint8 bytes[]) {
    requires cstr_readable(bytes);
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: precondition clause 1 of `strlen`
```
