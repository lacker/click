# Returning branches in sequence name the nesting bound

`f` allocates twelve cells, returning `-1` after freeing the earlier ones
when an allocation fails. The proof writes one `branch` per null check, in
sequence rather than nested: the `then` arm returns and the empty `else` arm
continues. Written this way the proof nests one region, but the two arms of
each `branch` end differently, so the driver runs the rest of the proof
inside the continuing `else` arm, one region deeper. Twelve such branches
reach one past the checked drivers' bound of eleven; eleven verify.

The driver used to report that bound as a shape "not implemented in this
execution context". It now names the bound and says why the depth grew.

```c filename=sequential_returning_branches.c
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
verifying "sequential_returning_branches.c";

int f() {
    ensures result == 18 or result == -1;
} by {
    step();
    step();
    branch {
        then {
            step();
            simp();
        }
        else {}
    }
    step();
    step();
    branch {
        then {
            step();
            step();
            simp();
        }
        else {}
    }
    step();
    step();
    branch {
        then {
            step();
            step();
            step();
            simp();
        }
        else {}
    }
    step();
    step();
    branch {
        then {
            step();
            step();
            step();
            step();
            simp();
        }
        else {}
    }
    step();
    step();
    branch {
        then {
            step();
            step();
            step();
            step();
            step();
            simp();
        }
        else {}
    }
    step();
    step();
    branch {
        then {
            step();
            step();
            step();
            step();
            step();
            step();
            simp();
        }
        else {}
    }
    step();
    step();
    branch {
        then {
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            simp();
        }
        else {}
    }
    step();
    step();
    branch {
        then {
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            simp();
        }
        else {}
    }
    step();
    step();
    branch {
        then {
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            simp();
        }
        else {}
    }
    step();
    step();
    branch {
        then {
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            simp();
        }
        else {}
    }
    step();
    step();
    branch {
        then {
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            simp();
        }
        else {}
    }
    step();
    step();
    branch {
        then {
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            simp();
        }
        else {}
    }
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    simp();
}
```

```expect
fail: this proof nests execution regions more deeply than the checked proof drivers support, at most 11
```
