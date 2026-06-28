# uint8 narrowing requires range proof

This checks that narrowing a symbolic `int32` into `uint8` is not accepted
without proof that the value is in byte range.

```c filename=uint8_narrowing_requires_range.c
uint8 narrow_return_missing_range(int32 x) {
    return x;
}
```

```click
verifying "uint8_narrowing_requires_range.c";

uint8 narrow_return_missing_range(int32 x) {
    ensures narrowed_return: result == x by auto;
}
```

```expect
fail: uint8 narrowing
```
