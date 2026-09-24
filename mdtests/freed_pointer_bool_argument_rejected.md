# Passing a freed pointer to a `_Bool` parameter is refused

Passing `p` to a `_Bool` parameter implicitly converts the pointer by testing
it against null. After `free(p)` that tests an indeterminate pointer value:
under C11 6.2.4p2 a pointer's value becomes indeterminate when its pointee's
lifetime ends, and Annex J.2 makes using that value undefined. Passing a freed
pointer to a pointer parameter only moves it; the conversion to `_Bool` at the
call boundary is refused like an explicit `(_Bool)p` cast, naming the freed
allocation; see `docs/concepts/undefined-behavior.md`.

```c filename=freed_bool_argument.c
void *malloc(unsigned long size);
void free(void *ptr);

int present(_Bool flag) {
    return flag;
}

int f(void) {
    int *p = malloc(sizeof(int));
    if (p == 0) {
        return -1;
    }
    free(p);
    return present(p);
}
```

```click
verifying "freed_bool_argument.c";

int present(bool flag) {
    ensures result == flag;
} by {
    execute();
    simp();
}

int f() {
    ensures result == 1 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
fail: use of a pointer into freed allocation heap-allocation:1000000
```
