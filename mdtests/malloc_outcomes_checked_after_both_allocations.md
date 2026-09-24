# Two allocations null-checked after both are made

Both `malloc` results are still undecided when the first `if` runs. The branch on `p != 0` decides only `p`'s outcome; `q`'s outcome stays pending in both arms until its own check. The checked `branch` used to refuse this ordinary shape with "cannot yet own an unresolved heap-allocation outcome split".

```c filename=two_outcomes.c
void *malloc(unsigned long size);
void free(void *ptr);

int f(void) {
    int *p = malloc(sizeof(int));
    int *q = malloc(sizeof(int));
    if (p != 0) {
        free(p);
    }
    if (q != 0) {
        free(q);
    }
    return 0;
}
```

```click
verifying "two_outcomes.c";

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
