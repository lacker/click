# Ordering pointers into a freed array is refused

`end` points one element into the same allocation as `p`; before the free `p < end` is defined and true. After `free(p)` both values are indeterminate, so the relational comparison is refused. Under C11 6.2.4p2 a pointer's value becomes indeterminate when its pointee's lifetime ends, and Annex J.2 makes using that value undefined. Click refuses the operation and names the freed allocation; see `docs/concepts/undefined-behavior.md`.

```c filename=freed_less.c
void *malloc(unsigned long size);
void free(void *ptr);

int f(void) {
    int *p = malloc(2 * sizeof(int));
    if (p == 0) {
        return -1;
    }
    int *end = p + 1;
    free(p);
    return p < end;
}
```

```click
verifying "freed_less.c";

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
