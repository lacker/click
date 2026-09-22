# int8 narrowing requires range proof

An `int32` value cannot be returned as `signed char` unless the verified contract
proves the signed 8-bit range.

```c filename=int8_narrowing_requires_range.c
signed char narrow_return_missing_range(int32 value) {
    return value;
}
```

```click
verifying "int8_narrowing_requires_range.c";

signed char narrow_return_missing_range(int32 value) {
    ensures narrowed_return: result == value by auto;
}
```

```expect
fail: int8 narrowing
```
