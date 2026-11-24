# a nested call precondition still requires every conjunct

The caller knows one arm of the callee's precondition. Explicit C steps use
the shared direct AND/OR rule, without a separate `have` or smart proof search.

```c filename=either.c
int32 caller(int32 x, int32 y) {
    int32 result;
    result = either_positive(x, y);
    return result;
}
```

```click
verifying "either.c";

extern int32 either_positive(int32 x, int32 y) {
    requires (x > 0 or y > 0) and (y < 0 or y > 0);
    ensures result == 0;
}

int32 caller(int32 x, int32 y) {
    requires x > 0;
    ensures result == 0 by {
        step();
        step();
        step();
        step();
        close();
    }
}
```

```expect
fail: unproved obligation: `(x > 0 or y > 0) and (y < 0 or y > 0)`
```
