# An `unsigned long long *` is not returned as an `unsigned long *`

A returned value converts to the return type as if by assignment (C11
6.8.6.4p3), and GCC 14 and Clang refuse the uncast conversion as incompatible
pointer types (`-Wincompatible-pointer-types`, an error by default in GCC 14).

```c filename=an_unsigned_long_long_pointer_is_not_returned_as_an_unsigned_long_pointer.c
unsigned long *view(unsigned long long *p) {
    return p;
}
```

```click
verifying "an_unsigned_long_long_pointer_is_not_returned_as_an_unsigned_long_pointer.c";

uint64 *view(uint64 *p) {
    ensures result == p by auto;
}
```

```expect
fail: incompatible C pointer types: expected `unsigned long *`, got `unsigned long long *`; long and long long are distinct types
```
