# omitted function effects do not preserve caller memory

An omitted function-level effect clause is an empty footprint. A callee that
writes a global must therefore be rejected at its own contract boundary,
rather than letting callers preserve stale values across the call.

```c filename=call_without_effect_clause_rejected.c
int32 g = 0;

int32 bump() {
    g = g + 1;
    return 0;
}
```

```click
verifying "call_without_effect_clause_rejected.c";

int32 bump() {
    requires g < 100;
    ensures result == 0;
}
```

```expect
fail: outside the mutable footprint
```
