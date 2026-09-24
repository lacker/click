# Freeing a pointer and not using it again verifies

The freed-pointer rule refuses operations on an indeterminate pointer value, not its mere existence: `p` stays in scope after `free(p)`, and `q`, a copy of it, stays in a local. Neither is compared, subtracted, tested or converted, so the function verifies.

```c filename=free_then_return.c
void *malloc(unsigned long size);
void free(void *ptr);

int f(void) {
    int *p = malloc(sizeof(int));
    if (p == 0) {
        return -1;
    }
    int *q = p;
    free(p);
    return 0;
}
```

```click
verifying "free_then_return.c";

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
