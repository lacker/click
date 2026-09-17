# Loop exits that reach different states join through the loop's binders

A loop statement has one successor, so the exits joined into it must be
described by one state. The guard-false exit stands at the loop's own exit
state, where every local the body writes is abstract; this `break` leaves after
assigning `r`, so the two exits do not agree on `r`. A23 refused exactly this.

The rule is decision D5 applied at the exits, the way the loop head and the
back edge apply it: the component the exits disagree about — here the local
`r` — becomes one fresh name, and each exit contributes, as its own disjunct,
what it established about that name. The guard-false exit's own facts are
restated about the successor's name (it reached the successor through the
head's value, and its own disjunct says so), so the exported disjunction is
`(i == 0 and r == 0) or r == 1` — the two ways out, in names a proof after the
loop can spell. `simp` reads the postcondition straight off it.

Nothing is assumed of an exit that did not state it: a claim the disjunction
does not support still fails, see
[`loop_body_break_exit_joined_state_rejected.md`](loop_body_break_exit_joined_state_rejected.md).

```c filename=assign_then_break.c
int32 assign_then_break(int32 n) {
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
verifying "assign_then_break.c";

int32 assign_then_break(int32 n) {
    requires n >= 0;
    ensures result == 0 or result == 1;
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

```termination
pending: unranked loop
```

```expect
pass
```
