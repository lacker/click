# The null arm of a deferred allocation check owns no memory

With a second allocation still pending, the `else` arm of `p != 0` sees `p` as the null pointer and owns nothing through it, so storing through `p` there is refused.

```c filename=null_arm.c
void *malloc(unsigned long size);
void free(void *ptr);

int f(void) {
    int *p = malloc(sizeof(int));
    int *q = malloc(sizeof(int));
    if (p != 0) {
        free(p);
    } else {
        *p = 1;
    }
    if (q != 0) {
        free(q);
    }
    return 0;
}
```

```click
verifying "null_arm.c";

int f() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `owns null@0[0..1]`
```
