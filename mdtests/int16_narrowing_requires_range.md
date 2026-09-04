# int16 narrowing requires range proof

An `int32` value cannot be returned as `short` unless the verified contract
proves the signed 16-bit range.

```c filename=int16_narrowing_requires_range.c
short narrow_return_missing_range(int32 value) {
    return value;
}
```

```click
verifying "int16_narrowing_requires_range.c";

short narrow_return_missing_range(int32 value) {
    ensures narrowed_return: result == value by auto;
}
```

```expect
fail: int16 narrowing
```
