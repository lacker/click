# A `long long *` is not assigned to an `unsigned long *`

The pointees differ in both rank and signedness; GCC 14 and Clang refuse the
uncast conversion as incompatible pointer types
(`-Wincompatible-pointer-types`, an error by default in GCC 14).

```c filename=a_long_long_pointer_is_not_assigned_to_an_unsigned_long_pointer.c
unsigned long *view(long long *p) {
    unsigned long *q = 0;
    q = p;
    return q;
}
```

```click
verifying "a_long_long_pointer_is_not_assigned_to_an_unsigned_long_pointer.c";

uint64 *view(int64 *p) {
    ensures result == p by auto;
}
```

```expect
fail: incompatible C pointer types: expected `unsigned long *`, got `long long *`; long and long long are distinct types
```
