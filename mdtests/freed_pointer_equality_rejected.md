# Comparing two copies of a freed pointer is refused

The smallest form of `byte_representation_freed_pointer_compare_rejected.md`: `q` copies `p`, `p` is freed, and the function returns `q == p`. Copying the pointer into `q` is fine; comparing the copies after the free is not. Under C11 6.2.4p2 a pointer's value becomes indeterminate when its pointee's lifetime ends, and Annex J.2 makes using that value undefined. Click refuses the operation and names the freed allocation; see `docs/concepts/undefined-behavior.md`.

```c filename=freed_equal.c
void *malloc(unsigned long size);
void free(void *ptr);

int f(void) {
    int *p = malloc(sizeof(int));
    if (p == 0) {
        return -1;
    }
    int *q = p;
    free(p);
    return q == p;
}
```

```click
verifying "freed_equal.c";

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
