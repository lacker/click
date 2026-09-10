# a caller that owns nothing cannot call a callee that owns the global

A caller with no resources owns nothing, so it cannot lend the callee the
global the callee owns, and cannot state the post-call value.

```c filename=call_without_ownership_caller_rejected.c
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
verifying "call_without_ownership_caller_rejected.c";

int32 bump() {
    requires g < 100;
    owns &g[0..1];
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
fail: missing resource fact `owns global:g@0[0..1]`
```
