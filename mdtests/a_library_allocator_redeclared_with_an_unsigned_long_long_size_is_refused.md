# A library allocator redeclared with an `unsigned long long` size is refused

`size_t` is `unsigned long` on x86-64 Linux. `unsigned long long` has the same
width but is a distinct type, so `void *malloc(unsigned long long)` is not
compatible with the C library's `void *malloc(size_t size)`; Clang diagnoses
the incompatible redeclaration of the library function. Click refuses the
declaration, while `void *malloc(unsigned long)` stays the library's own type.

```c filename=main.c
void *malloc(unsigned long long size);
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
fail: declaration of `malloc` has type `void * (unsigned long long)`, which is incompatible with the C library's `void *malloc(size_t size)`
```
