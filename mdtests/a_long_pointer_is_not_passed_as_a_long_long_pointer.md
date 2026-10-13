# A `long *` is not passed as a `long long *` argument

The argument converts to the parameter type as if by assignment (C11
6.5.2.2p7), and GCC 14 and Clang refuse the uncast conversion as incompatible
pointer types (`-Wincompatible-pointer-types`, an error by default in GCC 14).

```c filename=a_long_pointer_is_not_passed_as_a_long_long_pointer.c
long long read(long long *p) { return *p; }
long long view(long *p) {
    return read(p);
}
```

```click
verifying "a_long_pointer_is_not_passed_as_a_long_long_pointer.c";

int64 read(int64 *p) {
    views p[0];
    ensures result == p[0];
} by { execute(); simp(); }

int64 view(int64 *p) {
    views p[0];
    ensures result == p[0];
} by { execute(); simp(); }
```

```expect
fail: incompatible C pointer types: expected `long long *`, got `long *`; long and long long are distinct types
```
