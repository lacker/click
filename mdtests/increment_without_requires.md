# increment without an overflow precondition

This checks that `auto` refuses to prove `x + 1` for an unconstrained `int32 x`,
because signed overflow is possible in C.

```c filename=increment.c
int32 increment(int32 x) {
    return x + 1;
}
```

```click
verifying "increment.c";

int32 increment(int32 x) {
    ensures increments: result == x + 1 by auto;
}
```

```expect
fail: outcome was Ub(SignedOverflow)
```
