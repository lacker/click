# a caller can state a true post-call value when it owns the footprint

The modular rule is preserved by ownership: a caller may state the post-call
value when it owns the memory the callee can change.

```c filename=call_without_ownership_true_caller.c
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
verifying "call_without_ownership_true_caller.c";

int32 bump() {
    requires g < 100;
    owns &g[0..1];
    ensures result == 0;
    ensures g == old(g) + 1;
}

int32 caller() {
    requires g < 100;
    owns &g[0..1];
    ensures result == old(g) + 1;
} by {
    step();
    step();
    simp();
}
```

```expect
pass
```
