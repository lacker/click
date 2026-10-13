# A library function redeclared with an `int` result is refused

The parameter of this `strlen` declaration is the library's, but its result
is `int` rather than `size_t`, so the type is incompatible with the C
library's `size_t strlen(const char *s)` (C11 6.7.6.3p15). GCC 14 warns that
it conflicts with the built-in function and Clang that it is an incompatible
redeclaration of a library function; both reject it once `<string.h>` is
included. A call through it has undefined behavior, so Click refuses the
declaration rather than check the call against the library's contract.

```c filename=main.c
int strlen(const char *s);
int name_length(const char *s) {
    return strlen(s);
}
```

```click
target "x86_64-linux-userspace";
verifying "main.c";

int32 name_length(const char* s) {
    requires cstr_readable(s);
    ensures result >= 0;
} by {
    execute();
    simp();
}
```

```expect
fail: declaration of `strlen` has type `int32 (const char *)`, which is incompatible with the C library's `size_t strlen(const char *s)` (C11 6.7.6.3p15); Clang diagnoses it as an incompatible redeclaration of the library function, GCC and Clang reject it when the library's header is included, and Click specifies `strlen` only with the library's type; include `<string.h>` instead of declaring `strlen`, or declare it exactly as `size_t strlen(const char *s)`
```
