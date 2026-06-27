# C uint8 shifts rejected

This checks that C0 still rejects byte shifts until integer promotions and casts
are designed.

```c filename=shift_uint8_rejected.c
uint8 shift_uint8_rejected(uint8 x) {
    return x << 1;
}
```

```click
verifying "shift_uint8_rejected.c";

uint8 shift_uint8_rejected(uint8 x) {
    ensures no_promotions_yet: result == 0 by auto;
}
```

```expect
fail: RuntimeError(TypeMismatch)
```
