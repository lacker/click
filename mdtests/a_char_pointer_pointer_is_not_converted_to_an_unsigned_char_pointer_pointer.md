# A `char **` is not converted to an `unsigned char **`

Only one level of character pointer converts without a cast. `char **` and
`unsigned char **` point to pointer types that are not character types, and
GCC 14 and Clang refuse the uncast conversion as incompatible pointer types
(`-Wincompatible-pointer-types`, an error by default in GCC 14), so Click
refuses it too.

```c filename=a_char_pointer_pointer_is_not_converted_to_an_unsigned_char_pointer_pointer.c
unsigned char **retype(char **p) {
    return p;
}
```

```click
verifying "a_char_pointer_pointer_is_not_converted_to_an_unsigned_char_pointer_pointer.c";

unsigned char **retype(char **p) {
    ensures result == p by auto;
}
```

```expect
fail: incompatible C pointer types
```
