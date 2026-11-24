# Refolding an instance named like a C variable names the conflict

The contract names its instance `p`, like the C parameter. A proof binder
cannot hide a C variable, so the proof's `let p = fold(...)` cannot bind the
instance again under that name. The refusal names both bindings and the fix,
rather than only the C variable.

```c filename=instance_named_like_a_parameter.c
int32 get(int32* p) { return *p; }
```

```click
verifying "instance_named_like_a_parameter.c";

resource cell(p: int32*) {
    field v: int32;
    owns p[0..1];
    fact p[0] == v;
}

int32 get(int32* p) {
    owns p: cell(p);
    ensures result == p.v;
} by {
    let { v: pv } = unfold(p);
    step_until(function.exit);
    let p = fold(cell(p), { v: pv });
    close();
}
```

```expect
fail: names both a C variable and the contract's resource instance `p`
```
