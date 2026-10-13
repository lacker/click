# `size_t` and `int64_t` are `long` types in user space

On x86-64 Linux user space, glibc defines `size_t` as `unsigned long` and
`int64_t`/`uint64_t` as `long`/`unsigned long`, so pointers to them convert to
and from pointers to the `long` types without a cast, and a `void
*malloc(unsigned long)` declaration has the library's type. They are not `long
long`: `__builtin_types_compatible_p` tells the two apart, as GCC and Clang
do.

```c filename=main.c
#include <stddef.h>
#include <stdint.h>

void *malloc(unsigned long size);
void free(void *pointer);

unsigned long *sizes(size_t *p) {
    unsigned long *q = p;
    return q;
}

size_t *counts(unsigned long *p) {
    return p;
}

int64_t *values(long *p) {
    int64_t *q = p;
    return q;
}

unsigned long *words(uint64_t *p) {
    return p;
}

int allocate(void) {
    unsigned char *p = malloc(4);
    if (p == 0) { return 0; }
    free(p);
    return 1;
}

int identities(void) {
    return __builtin_types_compatible_p(size_t, unsigned long)
        && __builtin_types_compatible_p(int64_t, long)
        && __builtin_types_compatible_p(uint64_t, unsigned long)
        && !__builtin_types_compatible_p(int64_t, long long)
        && !__builtin_types_compatible_p(size_t, unsigned long long)
        && __builtin_types_compatible_p(long long *, long long int *)
        && !__builtin_types_compatible_p(long *, long long *);
}
```

```click
target "x86_64-linux-userspace";
verifying "main.c";

uint64 *sizes(uint64 *p) {
    ensures result == p by auto;
}

uint64 *counts(uint64 *p) {
    ensures result == p by auto;
}

int64 *values(int64 *p) {
    ensures result == p by auto;
}

uint64 *words(uint64 *p) {
    ensures result == p by auto;
}

int32 allocate() {
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}

int32 identities() {
    ensures result == 1 by { execute(); normalize(); }
}
```

```expect
pass
```
