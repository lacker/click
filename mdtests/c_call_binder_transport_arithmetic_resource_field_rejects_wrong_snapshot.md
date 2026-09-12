# Arithmetic cannot cross a resource-field snapshot implicitly

The post-call equality belongs to the call-exit resource state. Citing it
cannot establish an unrelated function-entry resource field.

```c filename=c_call_binder_transport_arithmetic_resource_field_wrong_snapshot.c
void increment(int32* state) { }
void caller(int32* state) { increment(state); }
```

```click
verifying "c_call_binder_transport_arithmetic_resource_field_wrong_snapshot.c";

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
    have at(function.entry, c.revision) == 1 by {
        arithmetic() using { c.revision == 1; }
    }
    execute();
    simp();
}
```

```expect
fail: current goal does not follow from exactly the listed arithmetic premises
```
