# A `static` function named `strlen` is the program's own

Without `<string.h>`, a translation unit may define a `static` function
named `strlen` (C11 7.1.3 reserves the name only for external linkage and,
with the header included, at file scope). GCC 14 and Clang accept it
without a diagnostic, and a call runs this body: it returns 0. Click
executes the body too; the library's contract for `strlen` does not apply,
so `last_index` returns 0 whatever the string.

```c filename=main.c
static unsigned long strlen(const char *s) {
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
    ensures result == 0u64;
} by {
    execute();
    simp();
}
```

```expect
pass
```
