# uint16 narrowing equals its source only in range

Returning an `int32` as `uint16_t` converts it modulo 65536, as GCC and Clang
do; no range is owed. The result is the source value only inside
`0..65535`, so claiming that equality for an unbounded `int32` is refused.

```c filename=uint16_narrowing_equals_its_source_only_in_range.c
uint16_t narrow_return_missing_range(int32 value) {
    return value;
}
```

```click
verifying "uint16_narrowing_equals_its_source_only_in_range.c";

uint16_t narrow_return_missing_range(int32 value) {
    ensures narrowed_return: result == value by auto;
}
```

```expect
fail: `ensures result == value` failed for `narrow_return_missing_range.narrowed_return`
```
