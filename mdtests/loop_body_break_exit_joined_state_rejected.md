# The joined exit states no more than its exits did

The positive sibling of
[`loop_body_break_exit_joined_state.md`](loop_body_break_exit_joined_state.md),
with the postcondition strengthened to a claim only one of the two exits
supports. The `break` exit explicitly proves `r == 1`. The guard-false exit
leaves with the `r` the invariant pins, `0`, so the written claim cannot
establish `result == 1` after the loop.

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

        initialize by close();
        maintain by {
            step();
            have r == 1 by close();
            step();
        }
    }
    step();
    close();
}
```

```expect
fail: unclosed goal: result == 1
```
