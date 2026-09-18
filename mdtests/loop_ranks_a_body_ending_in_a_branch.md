# the automatic preservation planner ranks a body that ends in a branch

`flip_to_n` counts to `n` and then flips `parity`, so the loop body's last
statement is a C `if` whose two arms fall straight through to the back edge.
The `loop` tactic writes no `preserve` body: the planner walks the body, splits
the branch, and closes the whole back-edge bundle on each arm — the two
declared invariants and the two members `decreases n - i;` adds, `0 <= n - i`
and a strict decrease.

Those ranking members are ordinary arithmetic over the loop head's own clauses,
so the automatic closer cites the same fixed premise list an explicit
`close_invariants()` would: the invariants and the guard read at iteration
entry, the function's `requires`, and the C branch condition this arm took.
Nothing here is searched for. Each arm's ranking member expands to an
`arithmetic_certificate`, and `click expand` reprints the closer as a proof
that re-verifies on its own.

```c filename=loop_ranks_a_body_ending_in_a_branch.c
int32 flip_to_n(int32 n) {
    int32 i = 0;
    int32 parity = 0;

    while (i < n) {
        i = i + 1;
        if (parity < 1) {
            parity = 1;
        } else {
            parity = 0;
        }
    }
    return parity;
}
```

```click
verifying "loop_ranks_a_body_ending_in_a_branch.c";

int32 flip_to_n(int32 n) {
    ensures result >= 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant parity >= 0 and parity <= 1;
        initialize by simp;
    }
    step();
    simp();
}
```

```expect
pass
```
