# A `long` object is not accessed through a `long long *` cast

GCC and Clang accept the explicit cast, but reading a `long` object through a
`long long` lvalue violates the effective-type rule (C11 6.5p7): `long long`
is neither the object's type nor its signed or unsigned variant, even though
it has the same representation. Click keeps refusing object-pointer casts that
retype the pointee, and with `long` and `long long` distinct this cast is one
of them.

```c filename=main.c
long long read_wide(long *p) {
    long long *q = (long long *)p;
    return *q;
}
```

```click
verifying "main.c";

int64 read_wide(int64 *p) {
    views p[0];
    ensures result == p[0];
} by { execute(); simp(); }
```

```expect
fail: incompatible C pointer types: retyping object-pointer casts are unsupported; expected `long long *`, got `long *`
```
