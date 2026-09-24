# Setting a freed pointer to null verifies

The common idiom `free(p); p = 0;` assigns a new value to `p` without using the indeterminate one, so it verifies, and `p` compares equal to null afterward. A later `if (p != 0) free(p);` therefore takes the null arm. Contrast `freed_pointer_null_comparison_rejected.md`, which compares `p` before reassigning it.

```c filename=free_then_null.c
void *malloc(unsigned long size);
void free(void *ptr);

int f(void) {
    int *p = malloc(sizeof(int));
    if (p == 0) {
        return -1;
    }
    free(p);
    p = 0;
    if (p != 0) {
        free(p);
        return 1;
    }
    return 0;
}
```

```click
verifying "free_then_null.c";

int f() {
    ensures result == 0 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
