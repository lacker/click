# A call map must bind every binder the callee declares

`increment` declares two instance binders. Omitting one from the map is an
error: the map is the only source of bindings, so nothing fills the gap.

```c filename=c_call_binder_transport_rejects_missing.c
void increment(int32* state) { }
void caller(int32* state) { increment(state); }
```

```click
verifying "c_call_binder_transport_rejects_missing.c";

resource Counter() { field revision: int32; }

void increment(int32* state) {
    owns first: Counter();
    owns second: Counter();
    ensures first.revision == 1;
    ensures second.revision == 1;
} by {
    unfold(first);
    unfold(second);
    execute();
    let first = fold(Counter(), { revision: 1 });
    let second = fold(Counter(), { revision: 1 });
    simp();
}

void caller(int32* state) {
    owns c: Counter();
    owns d: Counter();
    ensures c.revision == 1;
} by {
    step(increment(state), { first: c });
    execute();
    simp();
}
```

```expect
fail: call map omits `increment` binder `second`
```
