# A wrong `have` before a transported call is refused

The bridging `have` of `c_call_binder_transport_tighter_bound.md` is checked
where it stands, not waved through because the grouped proof accepts the
position. `c.revision < 500` does not follow from the caller's
`requires c.revision < 999`, so the proof fails at that tactic.

```c filename=c_call_binder_transport_wrong_have.c
void advance(int32* state) { }
void advance_once(int32* state) { advance(state); }
```

```click
verifying "c_call_binder_transport_wrong_have.c";

spec enum Mark { Clear, Set }
resource Counter() { field model: Mark; field revision: int32; }

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
    have c.revision < 500 by { simp(); }
    step(advance(state), { first: c });
    execute();
    simp();
}
```

```expect
fail: tactic 0: `have` failed
```
