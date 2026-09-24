# Comparing a freed pointer with null is refused

`p != 0` after `free(p)` is a comparison of an indeterminate pointer value, even though the other operand is the null pointer constant. Under C11 6.2.4p2 a pointer's value becomes indeterminate when its pointee's lifetime ends, and Annex J.2 makes using that value undefined. Click refuses the operation and names the freed allocation; see `docs/concepts/undefined-behavior.md`.

```c filename=freed_null.c
void *malloc(unsigned long size);
void free(void *ptr);

int f(void) {
    int *p = malloc(sizeof(int));
    if (p == 0) {
        return -1;
    }
    free(p);
    if (p != 0) {
        return 1;
    }
    return 0;
}
```

```click
verifying "freed_null.c";

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
