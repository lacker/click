# uint16 narrowing requires range proof

An `int32` value cannot be returned as `uint16_t` unless the verified contract
proves the unsigned 16-bit range.

```c filename=uint16_narrowing_requires_range.c
uint16_t narrow_return_missing_range(int32 value) {
    return value;
}
```

```click
verifying "uint16_narrowing_requires_range.c";

uint16_t narrow_return_missing_range(int32 value) {
    ensures narrowed_return: result == value by auto;
}
```

```expect
fail: uint16 narrowing
```
