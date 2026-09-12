# Post-call resource fields retain their checked snapshot

An exact resource-field equality produced by a transported call remains
source-expressible when it is cited by an arithmetic proof at the call exit.

```c filename=c_call_binder_transport_arithmetic_resource_field.c
void increment(int32* state) { }
void caller(int32* state) { increment(state); }
```

```click
verifying "c_call_binder_transport_arithmetic_resource_field.c";

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
    step(increment(state), { first: c });
    have at(statement(0).exit, c.revision) < 1000 by {
        arithmetic() using { c.revision == 1; }
    }
    execute();
    simp();
}
```

```expect
pass
```
