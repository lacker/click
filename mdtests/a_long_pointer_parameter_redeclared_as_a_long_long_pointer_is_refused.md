# A `long *` parameter redeclared as `long long *` is refused

`long *` and `long long *` point to distinct types, so a prototype taking one
and a definition taking the other conflict, as GCC and Clang report.

```c filename=main.c
void clear(long *p);
void clear(long long *p) { *p = 0; }
int run(int value) { return value; }
```

```click
verifying "main.c";

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail: conflicting declarations for function `clear`
```
