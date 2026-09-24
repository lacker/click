# Subtracting pointers into a freed array is refused

`end - p` is `1` while the array is live. After `free(p)` the difference uses two indeterminate pointer values and is refused. Under C11 6.2.4p2 a pointer's value becomes indeterminate when its pointee's lifetime ends, and Annex J.2 makes using that value undefined. Click refuses the operation and names the freed allocation; see `docs/concepts/undefined-behavior.md`.

```c filename=freed_diff.c
void *malloc(unsigned long size);
void free(void *ptr);

int f(void) {
    int *p = malloc(2 * sizeof(int));
    if (p == 0) {
        return -1;
    }
    int *end = p + 1;
    free(p);
    return (int)(end - p);
}
```

```click
verifying "freed_diff.c";

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
