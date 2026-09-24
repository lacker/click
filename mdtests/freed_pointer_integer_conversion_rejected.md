# Converting a freed pointer to an integer is refused

`(unsigned long)p` after `free(p)` converts an indeterminate pointer value. A pointer-to-pointer cast only retags the value, like a store, and is not refused; a conversion to an integer is. Under C11 6.2.4p2 a pointer's value becomes indeterminate when its pointee's lifetime ends, and Annex J.2 makes using that value undefined. Click refuses the operation and names the freed allocation; see `docs/concepts/undefined-behavior.md`.

```c filename=freed_cast.c
void *malloc(unsigned long size);
void free(void *ptr);

int f(void) {
    int *p = malloc(sizeof(int));
    if (p == 0) {
        return -1;
    }
    free(p);
    unsigned long address = (unsigned long)p;
    return address != 0ul;
}
```

```click
verifying "freed_cast.c";

int f() {
    ensures result == 1 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
fail: use of a pointer into freed allocation heap-allocation:1000000
```
