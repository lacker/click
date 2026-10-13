# int16 narrowing equals its source only in range

Returning an `int32` as `short` converts it modulo 65536, as GCC and Clang
do; no range is owed. The result is the source value only inside
`-32768..32767`, so claiming that equality for an unbounded `int32` is refused.

```c filename=int16_narrowing_equals_its_source_only_in_range.c
short narrow_return_missing_range(int32 value) {
    return value;
}
```

```click
verifying "int16_narrowing_equals_its_source_only_in_range.c";

short narrow_return_missing_range(int32 value) {
    ensures narrowed_return: result == value by auto;
}
```

```expect
fail: `ensures result == value` failed for `narrow_return_missing_range.narrowed_return`
```
