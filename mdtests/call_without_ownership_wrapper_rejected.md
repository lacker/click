# a caller that owns nothing cannot hide a mutating callee

The callee owns the global it writes, so the caller must own it too instead of
declaring no resources at all.

```c filename=call_without_ownership_wrapper_rejected.c
int32 g = 0;

int32 bump() {
    g = g + 1;
    return 0;
}

int32 wrapper() {
    bump();
    return 0;
}
```

```click
verifying "call_without_ownership_wrapper_rejected.c";

int32 bump() {
    requires g < 100;
    owns &g[0..1];
    ensures result == 0;
}

int32 wrapper() {
    requires g < 100;
    ensures result == 0;
}
```

```expect
fail: missing resource fact `owns global:g@0[0..1]`
```
