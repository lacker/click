# A six-allocation null-check chain expands

`f` allocates six cells. Each failed allocation frees the earlier ones and
returns `-1`; otherwise all six are freed and `f` returns `18`. `execute()`
splits at every null check, so `click expand` writes one proof `if` per check,
each nested in the previous one's `else` arm: six nested regions, well inside
the checked drivers' bound of eleven.

The rest of an arm, including the next proof `if` it ends at, continues that
arm's region. The structural driver used to charge that continuation a level
of its own, so every proof `if` cost two levels and the expanded proof was
declined at six allocations as a shape "not implemented in this execution
context". The expansion regression in `src/surface/tests/expansion_tests.rs`
expands this claim and re-verifies the rewrite.

```c filename=nested_null_check_chain.c
void *malloc(unsigned long size);
void free(void *ptr);

int f(void) {
    int *p0 = malloc(sizeof(int));
    if (p0 == 0) {
        return -1;
    }
    int *p1 = malloc(sizeof(int));
    if (p1 == 0) {
        free(p0);
        return -1;
    }
    int *p2 = malloc(sizeof(int));
    if (p2 == 0) {
        free(p0);
        free(p1);
        return -1;
    }
    int *p3 = malloc(sizeof(int));
    if (p3 == 0) {
        free(p0);
        free(p1);
        free(p2);
        return -1;
    }
    int *p4 = malloc(sizeof(int));
    if (p4 == 0) {
        free(p0);
        free(p1);
        free(p2);
        free(p3);
        return -1;
    }
    int *p5 = malloc(sizeof(int));
    if (p5 == 0) {
        free(p0);
        free(p1);
        free(p2);
        free(p3);
        free(p4);
        return -1;
    }
    free(p0);
    free(p1);
    free(p2);
    free(p3);
    free(p4);
    free(p5);
    return 18;
}
```

```click
verifying "nested_null_check_chain.c";

int f() {
    ensures result == 18 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
