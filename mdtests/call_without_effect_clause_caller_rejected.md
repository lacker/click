# a caller without an effect clause cannot preserve a changed global

An omitted effect clause on the caller is also an empty footprint when the
callee's certified effect summary is applied.

```c filename=call_without_effect_clause_caller_rejected.c
int32 g = 0;

int32 bump() {
    g = g + 1;
    return 0;
}

int32 caller() {
    bump();
    return g;
}
```

```click
verifying "call_without_effect_clause_caller_rejected.c";

int32 bump() {
    requires g < 100;
    mutable &g[0..1];
    ensures result == 0;
    ensures g == old(g) + 1;
}

int32 caller() {
    requires g < 100;
    ensures result == old(g) + 1;
} by {
    step();
    step();
    simp();
}
```

```expect
fail: outside the mutable footprint
```
