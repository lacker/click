# An `int **` does not convert to an `unsigned int **`

Only the first level of a pointer conversion may change an integer type's
signedness. GCC 14 rejects converting a pointer to `int *` into a pointer to
`unsigned int *` (`-Wincompatible-pointer-types`), and so does Click.

```c filename=an_int_pointer_pointer_does_not_convert_to_an_unsigned_int_pointer_pointer.c
int f(void) {
    int x = 0;
    int *p = &x;
    unsigned int **q = &p;
    return **q == 0;
}
```

```click
verifying "an_int_pointer_pointer_does_not_convert_to_an_unsigned_int_pointer_pointer.c";

int32 f() { ensures result == 1 by auto; }
```

```expect
fail: incompatible C pointer types: expected `uint32 **`, got `int32 **`; the signed and unsigned integer types of one width are distinct types
```
