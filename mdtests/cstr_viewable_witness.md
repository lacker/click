# C-string length witnesses carry viewability

`string::len` is an existentially usable description of a terminated byte
prefix. Its witness must also authorize the complete prefix, so a caller can
pass that range to a memory-reading external contract without separately
repeating the hidden length's viewability fact.

```c filename=cstr_loadable_witness.c
uint64 cstr_loadable_witness(uint8 source[], uint64 len) {
    return len;
}
```

```click
import click::c::string;

verifying "cstr_loadable_witness.c";

theorem cstr_len_exposes_viewable(source: uint8[], len: uint64) {
    requires string::len(source, len);

    ensures viewable(source[0..len + 1u64]) by {
        apply(string::len_is_viewable(source, len));
    }
}

uint64 cstr_loadable_witness(uint8 source[], uint64 len) {
    requires string::len(source, len);
    requires viewable(source[0..len + 1u64]);

    ensures result == len;
}
```

```expect
pass
```
