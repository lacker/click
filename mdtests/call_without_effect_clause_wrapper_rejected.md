# an immutable caller cannot hide a mutating callee

The callee declares its real footprint, so the caller must account for that
effect instead of claiming immutable.

```c filename=call_without_effect_clause_wrapper_rejected.c
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
verifying "call_without_effect_clause_wrapper_rejected.c";

int32 bump() {
    requires g < 100;
    mutable &g[0..1];
    ensures result == 0;
}

int32 wrapper() {
    requires g < 100;
    immutable;
    ensures result == 0;
}
```

```expect
fail: outside the mutable footprint
```
