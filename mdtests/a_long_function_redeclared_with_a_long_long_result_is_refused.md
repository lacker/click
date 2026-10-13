# A `long` function redeclared with a `long long` result is refused

`long` and `long long` have the same size and representation on x86-64 Linux,
but they are distinct C types, so the two declarations of `width` are not
compatible (C11 6.7.6.3p15) and GCC and Clang reject the redefinition as
conflicting types. Click refuses it too.

```c filename=main.c
long width(void);
long long width(void) { return 0; }
int run(int value) { return value; }
```

```click
verifying "main.c";

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail: conflicting declarations for function `width`
```
