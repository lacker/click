# Expansion refuses a rewrite past the nesting bound

`eleven` and `twelve` allocate eleven and twelve cells. Each failed
allocation frees the earlier ones and returns `-1`; otherwise every cell is
freed and the function returns `18`. `execute(); simp();` verifies both.

Expanding a whole claim writes one proof `if` per null check, each nested in
the previous one's `else` arm, with the closers at the leaves. For `eleven`
that is eleven nested regions, the checked drivers' bound, and the rewrite
re-verifies. For `twelve` it is one past the bound. `click expand` used to
emit that rewrite and only its reverification failed; expansion now refuses
it before emitting anything, with the verifier's nesting diagnostic and its
remedies. The expansion regression in `src/surface/tests/expansion_tests.rs`
pins both outcomes.

```c filename=null_check_chain_nesting.c
void *malloc(unsigned long size);
void free(void *ptr);

int eleven(void) {
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
    int *p6 = malloc(sizeof(int));
    if (p6 == 0) {
        free(p0);
        free(p1);
        free(p2);
        free(p3);
        free(p4);
        free(p5);
        return -1;
    }
    int *p7 = malloc(sizeof(int));
    if (p7 == 0) {
        free(p0);
        free(p1);
        free(p2);
        free(p3);
        free(p4);
        free(p5);
        free(p6);
        return -1;
    }
    int *p8 = malloc(sizeof(int));
    if (p8 == 0) {
        free(p0);
        free(p1);
        free(p2);
        free(p3);
        free(p4);
        free(p5);
        free(p6);
        free(p7);
        return -1;
    }
    int *p9 = malloc(sizeof(int));
    if (p9 == 0) {
        free(p0);
        free(p1);
        free(p2);
        free(p3);
        free(p4);
        free(p5);
        free(p6);
        free(p7);
        free(p8);
        return -1;
    }
    int *p10 = malloc(sizeof(int));
    if (p10 == 0) {
        free(p0);
        free(p1);
        free(p2);
        free(p3);
        free(p4);
        free(p5);
        free(p6);
        free(p7);
        free(p8);
        free(p9);
        return -1;
    }
    free(p0);
    free(p1);
    free(p2);
    free(p3);
    free(p4);
    free(p5);
    free(p6);
    free(p7);
    free(p8);
    free(p9);
    free(p10);
    return 18;
}

int twelve(void) {
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
    int *p6 = malloc(sizeof(int));
    if (p6 == 0) {
        free(p0);
        free(p1);
        free(p2);
        free(p3);
        free(p4);
        free(p5);
        return -1;
    }
    int *p7 = malloc(sizeof(int));
    if (p7 == 0) {
        free(p0);
        free(p1);
        free(p2);
        free(p3);
        free(p4);
        free(p5);
        free(p6);
        return -1;
    }
    int *p8 = malloc(sizeof(int));
    if (p8 == 0) {
        free(p0);
        free(p1);
        free(p2);
        free(p3);
        free(p4);
        free(p5);
        free(p6);
        free(p7);
        return -1;
    }
    int *p9 = malloc(sizeof(int));
    if (p9 == 0) {
        free(p0);
        free(p1);
        free(p2);
        free(p3);
        free(p4);
        free(p5);
        free(p6);
        free(p7);
        free(p8);
        return -1;
    }
    int *p10 = malloc(sizeof(int));
    if (p10 == 0) {
        free(p0);
        free(p1);
        free(p2);
        free(p3);
        free(p4);
        free(p5);
        free(p6);
        free(p7);
        free(p8);
        free(p9);
        return -1;
    }
    int *p11 = malloc(sizeof(int));
    if (p11 == 0) {
        free(p0);
        free(p1);
        free(p2);
        free(p3);
        free(p4);
        free(p5);
        free(p6);
        free(p7);
        free(p8);
        free(p9);
        free(p10);
        return -1;
    }
    free(p0);
    free(p1);
    free(p2);
    free(p3);
    free(p4);
    free(p5);
    free(p6);
    free(p7);
    free(p8);
    free(p9);
    free(p10);
    free(p11);
    return 18;
}
```

```click
verifying "null_check_chain_nesting.c";

int eleven() {
    ensures result == 18 or result == -1;
} by {
    execute();
    simp();
}

int twelve() {
    ensures result == 18 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
