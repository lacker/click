# A kernel-target definition of `strlen` is refused

The Linux kernel defines its own `strlen` in `lib/string.c`, but compiles
that file alone with `-ffreestanding` (`CFLAGS_string.o := -ffreestanding`
in Linux 6.8's `lib/Makefile`), so that GCC calls the body instead of
treating `strlen` as the library function. Every other x86-64 kernel file
is built hosted, and so is Click's `x86_64-linux-kernel` target, whose
fixed compiler profile is `-std=gnu11 -m64 -funsigned-char -nostdinc` with
neither `-ffreestanding` nor `-fno-builtin`. Under that profile GCC 14 and
Clang fold `strlen("abc")` to 3 at `-O0` whatever this body computes, so the
body below is not what a call means. Click refuses the definition on the
kernel target as on the user-space target, rather than verify a body the
compiler bypasses or bind the library's contract over it.

```c filename=main.c
typedef unsigned long size_t;
size_t strlen(const char *s) {
    size_t n = 0;
    while (s[n] != '\0') {
        n++;
    }
    return n;
}
size_t name_length(const char *name) {
    return strlen(name);
}
```

```click
target "x86_64-linux-kernel";
verifying "main.c";

uint64 name_length(const char* name) {
    requires cstr_readable(name);
    ensures name[result] == '\0';
} by {
    execute();
    simp();
}
```

```expect
fail: definition of the C library function `strlen` is not supported
```
