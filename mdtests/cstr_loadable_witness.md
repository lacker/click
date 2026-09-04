# C-string length witnesses carry loadability

`cstr_len` is an existentially usable description of a terminated byte
prefix. Its witness must also authorize the complete prefix, so a caller can
pass that range to a memory-reading external contract without separately
repeating the hidden length's loadability fact.

```c filename=cstr_loadable_witness.c
int32 cstr_loadable_witness(uint8 source[], int32 len) {
    return len;
}
```

```click
verifying "cstr_loadable_witness.c";

theorem cstr_len_exposes_loadable(source: uint8[], len: int32) {
    requires cstr_len(source, len);

    ensures loadable(source[0..len + 1]) by {
        apply(cstr_len_is_loadable(source, len));
    }
}

int32 cstr_loadable_witness(uint8 source[], int32 len) {
    requires cstr_len(source, len);
    requires loadable(source[0..len + 1]);

    ensures result == len;
} by {
    execute();
    simp();
}
```

```expect
pass
```
