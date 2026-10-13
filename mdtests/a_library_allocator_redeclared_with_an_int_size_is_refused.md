# A library allocator redeclared with an `int` size is refused

Calls to `malloc` follow Click's allocation model, which is the C library's
`void *malloc(size_t size)`. A program declaration of `malloc` with an `int`
parameter is incompatible with it (C11 6.7.6.3p15); GCC 14 and Clang
diagnose it as a conflicting redeclaration of the built-in function, and
reject it alongside `<stdlib.h>`. Click refuses the declaration.

```c filename=main.c
void *malloc(int size);
void free(void *pointer);
int allocate(void) {
    unsigned char *p = malloc(4);
    if (p == 0) { return 0; }
    free(p);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
verifying "main.c";

int32 allocate() {
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: declaration of `malloc` has type `void * (int32)`, which is incompatible with the C library's `void *malloc(size_t size)`
```
