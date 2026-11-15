# Post-call resource fields retain their checked state

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
    step_until(function.exit);
    let first = fold(Counter(), { revision: 1 });
    solve();
}

void caller(int32* state) {
    owns c: Counter();
    ensures c.revision == 1;
} by {
    step(increment, { first: c });
    have at(region(0).exit, c.revision) < 1000 by {
        solve() using { c.revision == 1; };
    }
}
```

```expect
pass
```
