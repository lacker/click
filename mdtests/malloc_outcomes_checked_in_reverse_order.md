# Two allocations null-checked in reverse allocation order

The later allocation is checked and freed first; the earlier one stays pending through that branch and its join.

```c filename=reverse_outcomes.c
void *malloc(unsigned long size);
void free(void *ptr);

int f(void) {
    int *p = malloc(sizeof(int));
    int *q = malloc(sizeof(int));
    if (q != 0) {
        free(q);
    }
    if (p != 0) {
        free(p);
    }
    return 0;
}
```

```click
verifying "reverse_outcomes.c";

int f() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
