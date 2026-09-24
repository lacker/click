# Deciding one allocation does not decide another

The `p != 0` arm decides only `p`; `q` has not been null-checked, so the arm owns no memory through it and storing through `q` is refused.

```c filename=other_pending.c
void *malloc(unsigned long size);
void free(void *ptr);

int f(void) {
    int *p = malloc(sizeof(int));
    int *q = malloc(sizeof(int));
    if (p != 0) {
        *q = 1;
        free(p);
    }
    if (q != 0) {
        free(q);
    }
    return 0;
}
```

```click
verifying "other_pending.c";

int f() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `owns symbolic-pointer:1000001@0[0..1]`
```
