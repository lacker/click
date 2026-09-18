# the smart closer ranks a loop that counts a parameter down

`n` is the function's parameter, the loop reassigns it, and an invariant
compares it with its value at loop entry. Splitting the invariant bundle
requires its written form to lower back to the kernel goal. The value `n`
held at entry was once written as the bare name `n`, which after the
reassignment names the new value, so the written bundle said `n <= n` for
`n <= at(drain.entry, n)`, lowered to another proposition, and `both` refused
to split it. A value the current locals cannot name is no longer spelled by
a parameter that has been reassigned; the ranking obligations then close from
the guard with nothing written but the clause.

```c filename=close_invariants_ranks_a_reassigned_parameter.c
int32 drain_to_zero(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
    return n;
}
```

```click
verifying "close_invariants_ranks_a_reassigned_parameter.c";

int32 drain_to_zero(int32 n) {
    requires n >= 0;
    requires n <= 100;
    ensures returns_zero: result == 0;
} by {
    loop as drain {
        decreases n;
        invariant n >= 0;
        invariant n <= at(drain.entry, n);
        preserve by {
            have 0 <= n - 1 by {
                apply(int32_positive_predecessor_is_nonnegative(n)) using { n > 0; }
            }
            have n <= at(drain.entry, n) by { assumption(); }
            have n - 1 <= at(drain.entry, n) by {
                arithmetic() using { n >= 0; n <= at(drain.entry, n); }
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
pass
```
