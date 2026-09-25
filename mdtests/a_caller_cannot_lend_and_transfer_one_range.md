# a caller cannot lend and transfer the same range in one call

The attack on the entry partition
(`docs/internals/resource-tracker.md`, "The entry partition"): `f` is the
body of `a_views_clause_is_separate_from_an_owns_clause.md`, which frames
`a[0]` across the store to `g[0]` because its `views` clause and its `owns`
clause denote disjoint memory. That fact is an assumption about `f`'s
environment, and every caller has to discharge it. `caller` passes `g`
itself as `a`, so it would have to lend a window into the very range it is
transferring.

The refusal comes from the call-site planner, which reserves every owned
requirement out of the caller's residual *before* it plans a single view
(`plan_stable_view_transfer_with_bindings_and_composites`,
`src/kernel/loans.rs`). It is fail-closed: a view whose backing owner is no
longer in the residual is refused for want of backing, never admitted.

```c filename=a_caller_cannot_lend_and_transfer_one_range.c
int32 g[4];

void f(int32 a[], int32 n) {
    g[0] = 1;
}

void caller() {
    f(g, 4);
}
```

```click
verifying "a_caller_cannot_lend_and_transfer_one_range.c";

void f(int32 a[], int32 n) {
    requires 0 < n;
    requires a[0] == 5;
    views a[0..n];
    owns g[0..1];
    ensures a[0] == 5;
    ensures g[0] == 1;
} by { execute(); simp(); }

void caller() {
    requires g[0] == 5;
    owns g[0..4];
    ensures g[0] == 5;
} by { execute(); have g[0] == 1 by { simp(); } simp(); }
```

```expect
fail: `caller.contract` tactic 0: `step()` could not verify C operation: stable-view a required resource overlaps a live borrowed footprint refused during planning; selected resource `owns global:g@0[0..4]`
```
