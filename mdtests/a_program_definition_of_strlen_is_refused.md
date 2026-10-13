# A program's definition of `strlen` is refused

C reserves the names of library functions for the library (C11 7.1.3), and
GCC 14 and Clang compile a call to `strlen` as a call to the library's
function whatever body the program supplies: both fold `strlen("abc")` to 3
even at `-O0` when the program's `strlen` returns 0, unless `-fno-builtin`
is given. Click checks each call against its specification of the library's
`strlen` and never verifies a program's body against that specification, so
it refuses the definition rather than ignore the body. A `static` function
of the same name is the program's own; see
`a_static_function_named_strlen_is_the_programs_own.md`.

```c filename=main.c
unsigned long strlen(const char *s) {
    return 0;
}
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
fail: definition of the C library function `strlen` is not supported
```
