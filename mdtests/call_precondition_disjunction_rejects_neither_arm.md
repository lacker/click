# an unestablished structured call precondition fails at its own obligation

Same callee as `call_precondition_disjunction_is_an_obligation`, with a caller
that establishes neither arm. The call raises the precondition as a required
verification condition, nothing discharges it, and the diagnostic names the
callee whose precondition it is.

```c filename=neither.c
int32 caller(int32 x, int32 y) {
    int32 result;
    result = either_positive(x, y);
    return result;
}
```

```click
verifying "neither.c";

extern int32 either_positive(int32 x, int32 y) {
    requires x > 0 or y > 0;
    ensures result == 0;
}

int32 caller(int32 x, int32 y) {
    ensures result == 0;
}
```

```expect
fail: either_positive precondition
```
