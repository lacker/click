# An unmapped caller instance frames across a binder-transporting call

The map is the whole binding. A second instance the caller owns but does not
mention keeps every field it had, while the mapped instance takes fresh
post-call fields related to entry only by the callee's guarantees.

```c filename=c_call_binder_transport_frames_other.c
void increment(int32* state) { }
void frames(int32* state) { increment(state); }
```

```click
verifying "c_call_binder_transport_frames_other.c";

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

void frames(int32* state) {
    owns c: Counter();
    owns other: Counter();
    ensures c.model == Mark::Set;
    ensures c.revision == 1;
    ensures other.model == old(other.model);
    ensures other.revision == old(other.revision);
} by {
    step(increment(state), { first: c });
    execute();
    simp();
}
```

```expect
pass
```
