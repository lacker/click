# A mapped name must be an instance the caller owns

The map binds a callee binder to an instance of the caller. A name that is
not an owned resource instance is rejected where it is written.

```c filename=c_call_binder_transport_rejects_unowned.c
void increment(int32* state) { }
void caller(int32* state) { increment(state); }
```

```click
verifying "c_call_binder_transport_rejects_unowned.c";

resource Counter() { field revision: int32; }

void increment(int32* state) {
    owns first: Counter();
    ensures first.revision == 1;
} by {
    unfold(first);
    execute();
    let first = fold(Counter(), { revision: 1 });
    simp();
}

void caller(int32* state) {
    owns c: Counter();
    ensures c.revision == 1;
} by {
    step(increment(state), { first: state });
    execute();
    simp();
}
```

```expect
fail: unknown resource instance `state`
```
