# A transported instance returns with fresh fields, not its old ones

Returning ownership keeps the instance's identity, not its field values. A
field the callee's guarantees do not mention is unknown after the call, so
the caller cannot claim it is unchanged.

```c filename=c_call_binder_transport_rejects_no_implicit_preservation.c
void increment(int32* state) { }
void caller(int32* state) { increment(state); }
```

```click
verifying "c_call_binder_transport_rejects_no_implicit_preservation.c";

resource Counter() { field revision: int32; field created: int32; }

void increment(int32* state) {
    owns first: Counter();
    ensures first.revision == 1;
} by {
    unfold(first);
    execute();
    let first = fold(Counter(), { revision: 1, created: old(first.created) });
    simp();
}

void caller(int32* state) {
    owns c: Counter();
    ensures c.created == old(c.created);
} by {
    step(increment(state), { first: c });
    execute();
    simp();
}
```

```expect
fail: unclosed goal: c.created == old(c.created)
```
