# A live pointer converts to `_Bool` at a return and a call after another free

Returning a pointer from a `_Bool` function, or passing it to a `_Bool`
parameter, converts it by testing it against null. Freeing a different
allocation first does not make that pointer indeterminate: `returned` frees
its own scratch allocation and still returns the live parameter as `1`, and
`passed` frees one allocation and then passes the other, still live, to a
`_Bool` parameter whose precondition requires `1`. This is the control for
`freed_pointer_bool_return_rejected.md` and
`freed_pointer_bool_argument_rejected.md`, which make the same conversions on
the pointer that was freed.

```c filename=live_bool.c
void *malloc(unsigned long size);
void free(void *ptr);

int present(_Bool flag) {
    return flag;
}

_Bool returned(int *p) {
    int *q = malloc(sizeof(int));
    if (q == 0) {
        return p;
    }
    free(q);
    return p;
}

int passed(void) {
    int *q = malloc(sizeof(int));
    if (q == 0) {
        return 1;
    }
    int *p = malloc(sizeof(int));
    if (p == 0) {
        free(q);
        return 1;
    }
    free(q);
    int result = present(p);
    free(p);
    return result;
}
```

```click
verifying "live_bool.c";

int present(bool flag) {
    requires flag == 1;
    ensures result == 1;
} by {
    execute();
    simp();
}

bool returned(int *p) {
    requires p != 0;
    ensures result == 1;
} by {
    execute();
    simp();
}

int passed() {
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
