# A `long *` does not initialize a `long long *`

Both point to 64-bit integers, but `long` and `long long` are distinct types,
so GCC 14 and Clang refuse the uncast conversion as incompatible pointer types
(`-Wincompatible-pointer-types`, an error by default in GCC 14). Click refuses
it too.

```c filename=a_long_pointer_does_not_initialize_a_long_long_pointer.c
long long *view(long *p) {
    long long *q = p;
    return q;
}
```

```click
verifying "a_long_pointer_does_not_initialize_a_long_long_pointer.c";

int64 *view(int64 *p) {
    ensures result == p by auto;
}
```

```expect
fail: incompatible C pointer types: expected `long long *`, got `long *`; long and long long are distinct types
```
