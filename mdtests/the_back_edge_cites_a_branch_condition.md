# the smart closer cites the C branch conditions the body took

`stop_at_zero` leaves through a `break` inside an `if`, so the only path that
reaches the back edge is the one where `i == 0` was false. That decision is
what makes the measure decrease: `decreases i;` owes `0 < i` at iteration
entry, and the declared invariant gives only `0 <= i`.

Nothing in the loop head says `i != 0`. The C `if` does, and the body took its
else arm, so the closer may name it: a branch the path took is as written as
the loop guard is. The back edge's closer records each branch condition where the
path decided it, at that statement's entry state, and names it beside the
invariants and the guard — a fixed, small list per path, not a search over the
facts in scope. Here the cells the condition read are unchanged since iteration
entry, so the premise is cited in the iteration-entry spelling the invariant
already uses and `less_than_from_not_equal` pairs the two.

```c filename=the_back_edge_cites_a_branch_condition.c
int32 stop_at_zero(int32 n) {
    int32 i = n;

    while (true) {
        if (i == 0) {
            break;
        }
        i = 0;
    }
    return i;
}
```

```click
verifying "the_back_edge_cites_a_branch_condition.c";

int32 stop_at_zero(int32 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    step();
    step();
    loop {
        decreases i;
        invariant i >= 0;
    }
    step();
    solve();
}
```

```expect
pass
```
