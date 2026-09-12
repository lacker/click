# A `branch` arm that breaks has nothing to join

`branch` joins its two arms at the statement after the C `if`. An arm that
leaves the loop through `break` never arrives there: its path ends at the loop
rule as an exit, while the other arm runs on to the back edge. Joining them
would export one successor for two paths that go to different places, so the
rule refuses and names the spelling that keeps them apart — the proof-level
`if`, whose arms each reach the loop rule on their own and are never joined
across the back edge.

[`loop_body_break_exit.md`](loop_body_break_exit.md) is the same C written that
way.

```c filename=branch_arm_break.c
int32 branch_arm_break(int32 n) {
    int32 i = n;

    while (true) {
        if (i == 3) {
            break;
        }
        i = 3;
    }
    return i;
}
```

```click
verifying "branch_arm_break.c";

int32 branch_arm_break(int32 n) {
    requires n >= 0;
    ensures result == 3;
} by {
    step();
    step();
    loop {
        invariant i >= 0;

        initialize by simp;
        preserve by {
            branch {
                then { step(); }
                else { }
            }
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
fail: `branch` arm's `break` leaves the loop
```
