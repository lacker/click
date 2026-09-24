# A null-guarded free and a live pointer's null test verify

`if (p != 0) free(p);` compares `p` while it is live, so the guard is defined. After `p` is freed, `q`, a distinct live allocation, is still compared with null and freed: the freed-pointer rule concerns only pointers into the freed allocation.

```c filename=guarded_free.c
void *malloc(unsigned long size);
void free(void *ptr);

int f(void) {
    int *q = malloc(sizeof(int));
    if (q == 0) {
        return -1;
    }
    int *p = malloc(sizeof(int));
    if (p != 0) {
        free(p);
    }
    if (q != 0) {
        free(q);
        return 1;
    }
    return 0;
}
```

```click
verifying "guarded_free.c";

int f() {
    ensures result == 1 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
