# Three allocations null-checked after all are made

Each branch decides exactly one pending allocation outcome and leaves the later ones pending.

```c filename=three_outcomes.c
void *malloc(unsigned long size);
void free(void *ptr);

int f(void) {
    int *p = malloc(sizeof(int));
    int *q = malloc(sizeof(int));
    int *r = malloc(sizeof(int));
    if (p != 0) {
        free(p);
    }
    if (q != 0) {
        free(q);
    }
    if (r != 0) {
        free(r);
    }
    return 0;
}
```

```click
verifying "three_outcomes.c";

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
