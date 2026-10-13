# A library function redeclared with an `int` parameter is refused

Click checks a call to `strlen` against its specification of the C
library's `size_t strlen(const char *s)`, which binds by the function's name.
This program declares `strlen` itself with an `int` parameter, a type
incompatible with the library's (C11 6.7.6.3p15), and then passes it a
pointer. GCC 14 and Clang reject the call (`-Wint-conversion` is an error)
and diagnose the declaration as a conflicting or incompatible redeclaration
of the library function. Click refuses the declaration, naming its type and
the library's, instead of binding the library's contract to it.

```c filename=main.c
int strlen(int s);
unsigned long last_index(const char *s) {
    unsigned long n = strlen(s);
    return n;
}
```

```click
target "x86_64-linux-userspace";
verifying "main.c";

uint64 last_index(const char* s) {
    requires cstr_readable(s);
    ensures s[result] == '\0';
} by {
    execute();
    simp();
}
```

```expect
fail: declaration of `strlen` has type `int32 (int32)`, which is incompatible with the C library's `size_t strlen(const char *s)`
```
