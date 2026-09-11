# A `have` bridges a tighter caller bound around a transported call

`advance` requires `first.revision < 1000` of the instance it owns, and the
exact-route policy on resource-field requirements is deliberate: a caller that
knows only `c.revision < 999` has to bridge the two bounds itself. The bridge
is a `have` written in the grouped contract proof, so a grouped proof accepts
`have` wherever an execution step may stand — before the first step
(`advance_once`) and between two steps (`run_twice`) — with the scoping it has
after `execute()`.

```c filename=c_call_binder_transport_tighter_bound.c
void increment(int32* state) { }
void advance(int32* state) { }
void advance_once(int32* state) { advance(state); }
void run_twice(int32* state) { increment(state); increment(state); }
```

```click
verifying "c_call_binder_transport_tighter_bound.c";

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

void advance_once(int32* state) {
    owns c: Counter();
    requires c.revision < 999;
    ensures c.model == old(c.model);
    ensures c.revision == old(c.revision) + 1;
} by {
    have c.revision < 1000 by { simp(); }
    step(advance(state), { first: c });
    execute();
    simp();
}

void run_twice(int32* state) {
    owns c: Counter();
    requires c.revision < 999;
    ensures c.model == Mark::Set;
    ensures c.revision == 1;
} by {
    step(increment(state), { first: c });
    have c.revision == 1 by { simp(); }
    step(increment(state), { first: c });
    execute();
    simp();
}
```

```expect
pass
```
