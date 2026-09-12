# The joined exit states no more than its exits did

The positive sibling of
[`loop_body_break_exit_joined_state.md`](loop_body_break_exit_joined_state.md),
with the postcondition strengthened to a claim only one of the two exits
supports. The `break` exit leaves with `r == 1`; the guard-false exit leaves
with the `r` the invariant pins, `0`. The join gives `r` one fresh name and
exports the disjunction of what each exit said about it, so `result == 1` is
not available: the rule weakens, it does not pick a favourite exit.

```c filename=assign_then_break_claim.c
int32 assign_then_break_claim(int32 n) {
    int32 i = n;
    int32 r = 0;

    while (i != 0) {
        r = 1;
        break;
    }
    return r;
}
```

```click
verifying "assign_then_break_claim.c";

int32 assign_then_break_claim(int32 n) {
    requires n >= 0;
    ensures result == 1;
} by {
    step();
    step();
    step();
    step();
    loop {
        invariant i >= 0;
        invariant r == 0;

        initialize by simp;
        preserve by {
            step();
            step();
        }
    }
    step();
    simp();
}
```

```expect
fail: unclosed goal: result == 1
```
