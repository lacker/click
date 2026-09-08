# a sidecar literal above `INT32_MAX` is not the negative bit pattern

The negative half of `sidecar_literal_types_match_c.md`. A function returning
`INT32_MIN` does not satisfy a postcondition naming 2147483648: those are
different values, as they are in C, where the literal is a `long`.

```c filename=sidecar_literal_above_int32_rejected.c
int32 sidecar_literal_above_int32_rejected(int32 x) {
    return x;
}
```

```click
verifying "sidecar_literal_above_int32_rejected.c";

int32 sidecar_literal_above_int32_rejected(int32 x) {
    requires x == -2147483648;
    ensures result == 2147483648;
}
```

```expect
fail: unclosed goal
```
