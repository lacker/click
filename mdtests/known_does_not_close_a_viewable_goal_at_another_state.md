# `known()` does not close a `viewable` goal from another state

`viewable(b[0..n])` before the store to `b[0]` names the memory before the
store; the same spelling after it names the memory after it. They are
different facts, and carrying one across the store is `transport`'s job, not
`known()`'s. `known()` closes a goal only from the identical
available fact (`mdtests/known_closes_an_established_viewable_fact.md`).

```c filename=known_does_not_close_a_viewable_goal_at_another_state.c
int32 probe(int32 b[], int32 n) {
    b[0] = 1;
    return 0;
}
```

```click
verifying "known_does_not_close_a_viewable_goal_at_another_state.c";

int32 probe(int32 b[], int32 n) {
    requires 1 <= n;
    requires n <= 1073741823;
    owns b[0..n];
    ensures result == 0;
} by {
    have viewable(b[0..n]);
    step();
    have viewable(b[0..n]) by known();
    step();
    solve();
}
```

```expect
fail: `known()` could not close the current goal
```
