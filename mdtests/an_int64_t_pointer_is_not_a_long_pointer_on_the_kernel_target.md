# An `int64_t *` is not a `long *` on the kernel target

The kernel's `int64_t` is `long long`, so on the `x86_64-linux-kernel` target
a pointer to it does not convert to `long *` without a cast, as GCC 14 and
Clang refuse when building the kernel. The same program is accepted for user
space, where glibc's `int64_t` is `long`.

```c filename=main.c
long *values(int64_t *p) {
    return p;
}
```

```click
target "x86_64-linux-kernel";
verifying "main.c";

int64 *values(int64 *p) {
    ensures result == p by auto;
}
```

```expect
fail: incompatible C pointer types: expected `long *`, got `long long *`; long and long long are distinct types
```
