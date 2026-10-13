# uint8 narrowing equals its source only in range

Returning an `int32` as `uint8` converts it modulo 256, as GCC and Clang
do; no range is owed. The result is the source value only inside
`0..255`, so claiming that equality for an unbounded `int32` is refused.
`mdtests/uint8_narrowing.md` proves it under the range.

```c filename=uint8_narrowing_equals_its_source_only_in_range.c
uint8 narrow_return_missing_range(int32 x) {
    return x;
}
```

```click
verifying "uint8_narrowing_equals_its_source_only_in_range.c";

uint8 narrow_return_missing_range(int32 x) {
    ensures narrowed_return: result == x by auto;
}
```

```expect
fail: `ensures result == x` failed for `narrow_return_missing_range.narrowed_return`
```
