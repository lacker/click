# A call map cannot bind an instance a previous call consumed

`take` consumes its `Counter` binder. The caller binds `c` to it, then binds the
same `c` to `advance`'s binder. The kernel checks the map against what the
caller owns at the second call, where `c` is gone, and refuses with the same
refusal a named contract's proof argument gets
(`c_named_contract_rejects_consumed_instance.md`): both forms bind through one
checked constructor.

```c filename=c_call_binder_transport_rejects_consumed_instance.c
void take(int32* state) { }
void advance(int32* state) { }
void take_then_advance(int32* state) { take(state); advance(state); }
```

```click
verifying "c_call_binder_transport_rejects_consumed_instance.c";

resource Counter() { field revision: int32; }

void take(int32* state) {
    consumes t: Counter();
} by {
    execute();
    simp();
}

void advance(int32* state) {
    owns first: Counter();
    ensures first.revision == old(first.revision);
} by {
    execute();
    simp();
}

void take_then_advance(int32* state) {
    consumes c: Counter();
} by {
    step(take(state), { t: c });
    step(advance(state), { first: c });
    execute();
    simp();
}
```

```expect
fail: resource proof argument is not owned
```
