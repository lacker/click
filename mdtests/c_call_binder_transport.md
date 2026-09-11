# A C call transports the callee's named instance binders

An ordinary C call to a function whose sidecar declares instance binders
carries them through the call map: `step(increment(state), { first: c })`
binds the callee's binder `first` to the caller's own instance `c`.
`run_twice` supplies the same instance to two calls, so the first call has to
return ownership of it. `advance_once` shows the transported instance keeping
its identity, with post-call fields related to entry only by the callee's own
guarantee.

```c filename=c_call_binder_transport.c
void increment(int32* state) { }
void advance(int32* state) { }
void run_twice(int32* state) { increment(state); increment(state); }
void advance_once(int32* state) { advance(state); }
```

```click
verifying "c_call_binder_transport.c";

spec enum Mark { Clear, Set }
resource Counter() { field model: Mark; field revision: int32; }

void increment(int32* state) {
    owns first: Counter();
    ensures first.model == Mark::Set;
    ensures first.revision == 1;
} by {
    unfold(first);
    execute();
    let first = fold(Counter(), { model: Mark::Set, revision: 1 });
    simp();
}

void advance(int32* state) {
    owns first: Counter();
    requires first.revision < 1000;
    ensures first.model == old(first.model);
    ensures first.revision == old(first.revision) + 1;
} by {
    unfold(first);
    execute();
    let first = fold(Counter(), { model: old(first.model), revision: old(first.revision) + 1 });
    simp();
}

void run_twice(int32* state) {
    owns c: Counter();
    ensures c.model == Mark::Set;
    ensures c.revision == 1;
} by {
    step(increment(state), { first: c });
    step(increment(state), { first: c });
    execute();
    simp();
}

void advance_once(int32* state) {
    owns c: Counter();
    requires c.revision < 1000;
    ensures c.model == old(c.model);
    ensures c.revision == old(c.revision) + 1;
} by {
    step(advance(state), { first: c });
    execute();
    simp();
}
```

```expect
pass
```
