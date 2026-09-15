# A call map cannot bind one instance to two binders

`pair_step` declares two `Counter` binders. Binding the caller's single `c` to
both is refused where the map is written: an exclusive instance supplies at
most one binder of a call. The kernel checks the same rule again when it binds
the map (`direct_call_map_is_checked_in_kernel_like_named_proof_arguments`), so
a transport the surface did not see cannot pass it either.

```c filename=c_call_binder_transport_rejects_shared_instance.c
void pair_step(int32* state) { }
void run_pair(int32* state) { pair_step(state); }
```

```click
verifying "c_call_binder_transport_rejects_shared_instance.c";

spec enum Mark { Clear, Set }

resource Counter() { field model: Mark; field revision: int32; }

void pair_step(int32* state) {
    owns first: Counter();
    owns second: Counter();
    ensures first.revision == old(first.revision);
    ensures second.revision == old(second.revision);
} by {
    execute();
    simp();
}

void run_pair(int32* state) {
    owns c: Counter();
    ensures c.revision == old(c.revision);
} by {
    step(pair_step(state), { first: c, second: c });
    execute();
    simp();
}
```

```expect
fail: cannot supply two binders of `pair_step`
```
