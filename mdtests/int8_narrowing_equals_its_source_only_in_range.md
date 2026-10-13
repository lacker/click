# int8 narrowing equals its source only in range

Returning an `int32` as `signed char` converts it modulo 256, as GCC and Clang
do; no range is owed. The result is the source value only inside
`-128..127`, so claiming that equality for an unbounded `int32` is refused.
`mdtests/int8_conversion.md` proves it under the range.

```c filename=int8_narrowing_equals_its_source_only_in_range.c
signed char narrow_return_missing_range(int32 value) {
    return value;
}
```

```click
verifying "int8_narrowing_equals_its_source_only_in_range.c";

signed char narrow_return_missing_range(int32 value) {
    ensures narrowed_return: result == value by auto;
}
```

```expect
fail: `ensures result == value` failed for `narrow_return_missing_range.narrowed_return`
```
