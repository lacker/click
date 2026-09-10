# The closing simp returns a composite the body holds in pieces

The body owns `p[0..1]` and has stored `1` there, which is exactly the body
of `initialized(p)`. The closing `simp` reads the exit through the contract's
resource transition once the body establishes every returned resource
definitionally, the same rule contract certification applies to a
`produces` claim, so the explicit `fold` after it is not what closes the
claim. A body that does not hold a returned resource still fails at the
resource ensure (`permission_call_consumes_write_without_return.md`).

```c filename=grouped_fold_order.c
int32 initialize(int32 p[]) {
    p[0] = 1;
    return 1;
}
```

```click
resource initialized(p: int32*) {
    owns p[0..1];
    fact p[0] == 1;
}

verifying "grouped_fold_order.c";

int32 initialize(int32 p[]) {
    consumes p[0..1];
    produces initialized(p);
} by {
    execute();
    simp();
    fold(initialized(p));
}
```

```expect
pass
```
