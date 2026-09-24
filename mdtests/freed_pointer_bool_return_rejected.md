# Returning a freed pointer from a `_Bool` function is refused

`return p;` in a function returning `_Bool` implicitly converts the pointer by
testing it against null. After `free(p)` that tests an indeterminate pointer
value: under C11 6.2.4p2 a pointer's value becomes indeterminate when its
pointee's lifetime ends, and Annex J.2 makes using that value undefined. The
conversion at the return boundary is refused like an explicit `(_Bool)p` cast,
naming the freed allocation; see `docs/concepts/undefined-behavior.md`.

```c filename=freed_bool_return.c
void *malloc(unsigned long size);
void free(void *ptr);

_Bool f(void) {
    int *p = malloc(sizeof(int));
    if (p == 0) {
        return 0;
    }
    free(p);
    return p;
}
```

```click
verifying "freed_bool_return.c";

bool f() {
    ensures result == 1 or result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: use of a pointer into freed allocation heap-allocation:1000000
```
