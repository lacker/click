# A loop proof after a proof-level `branch` expands

`count_after_guard` returns early for a non-positive `n` and then counts up
to `n`. The proof splits the early return with a proof-level `branch`, then
states the loop. A loop is one tactic of the rest of the proof, and the
tactics of its `initialize` and `preserve` proofs are numbered directly
after it.

Expanding the `initialize by simp` site used to fail although verification
accepted the proof: the structural checked driver asked whether the rest of
the proof after the `branch` held the selected tactic, compared only each
linear tactic's own index, missed the tactic nested in the loop, and
declined the `branch`, so expansion reported that a proof-level `branch` is
not implemented in this execution context. The same shape in `arena_init`
(`examples/arena`) failed `click audit`. The expansion regression in
`src/surface/tests/expansion_tests.rs` expands the site and re-verifies the
rewrite, and the audit regression in `src/bin/click-audit/tests.rs` audits
every smart site of this file.

```c filename=count_after_guard.c
int32 count_after_guard(int32 n) {
    int32 i;
    if (n <= 0) {
        return 0;
    }
    i = 0;
    while (i < n) {
        i++;
    }
    return i;
}
```

```click
verifying "count_after_guard.c";

int32 count_after_guard(int32 n) {
    requires n >= 0 and n <= 2147483647;
    ensures result >= 0;
} by {
    step();
    branch {
        then {
            step();
            simp();
        }
        else {}
    }
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
        initialize by simp;
        preserve by {
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
