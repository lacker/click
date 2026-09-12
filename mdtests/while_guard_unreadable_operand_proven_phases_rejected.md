# A proven-phase loop still cannot drop an unreadable guard operand

This is the same unreadable second conjunct as
`while_guard_unreadable_operand_rejected.md`, but with `initialize by` and
`preserve by` discharged separately. Once both phases are proven the loop rule
computes its exit paths without re-running preservation, so the exit assumption
is the only thing standing between the proof and `result == 0`. Dropping the
operand that cannot be read would make that assumption `a == 0` alone, which is
not the negation of the guard.

```c filename=while_guard_unreadable_operand_proven_phases_rejected.c
int32 uprec_phases(int32 a, int32 *p) {
    while (a != 0 && p[0] != 0) {
        a = 0;
    }
    return a;
}
```

```click
verifying "while_guard_unreadable_operand_proven_phases_rejected.c";

int32 uprec_phases(int32 a, int32* p) {
    requires a >= 0;
    requires a <= 10;
    ensures result == 0;
} by {
    loop {
        invariant a >= 0;
        invariant a <= 10;
        initialize by simp;
        preserve by {
            step();
            close_invariants by {
                both { simp(); } and { simp(); }
            }
        }
    }
    step();
    simp();
}
```

```expect
fail: the loop condition could not be evaluated
```
