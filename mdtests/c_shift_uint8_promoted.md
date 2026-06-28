# C uint8 shifts promoted

This checks that C0 promotes `uint8` operands before shifting. The promoted
byte range also proves that shifting left by one does not overflow.

```c filename=shift_uint8_promoted.c
int32 shift_uint8_promoted(uint8 x) {
    return x << 1;
}
```

```click
verifying "shift_uint8_promoted.c";

function byte_shl1(uint8 x) -> int32 {
    x << 1
}

int32 shift_uint8_promoted(uint8 x) {
    ensures promoted_shift: result == byte_shl1(x) by auto;
}
```

```expect
pass
```
