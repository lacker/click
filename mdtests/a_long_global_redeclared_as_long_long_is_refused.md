# A `long` global redeclared as `long long` is refused

The two declarations of `total` give it distinct types, `long` and `long
long`, which GCC and Clang reject as conflicting types even though both are
64-bit integers.

```c filename=main.c
extern long total;
long long total;
int run(int value) { return value; }
```

```click
verifying "main.c";

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail: conflicting declarations for global `total`
```
