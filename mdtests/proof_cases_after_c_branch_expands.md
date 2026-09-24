# A proof `cases` after a C branch expands

`pick` returns `18` or `-1`, and `use_pick` returns `0` for a negative
result and the result otherwise. The caller proof splits on `result == 0`
after `execute()`. Its `else` arm proves `result == 18` with a `cases` on
`pick`'s disjunctive postcondition, closing the `-1` case by contradiction.

The proof `if` splits the non-negative C path into two outcomes, so the
`result == 0` arm is reached both from the `copied < 0` branch and from the
fall-through branch, and `simp()` closes it differently on each. Claim
expansion used to synthesize the proof cases across all outcomes at once,
found two outcomes in one proof arm with different closers and no proof-level
condition between them, and refused with "distinct certified paths have no
surface branch condition", although verification and `click audit` accepted
the proof. The C branch already separates those outcomes: expansion now
places the proof cases inside each C branch arm, from exactly the outcomes
that reach it. The expansion regression in
`src/surface/tests/expansion_tests.rs` expands this claim and re-verifies the
rewrite.

```c filename=pick_cases.c
int pick(int x) {
    if (x > 0) {
        return 18;
    }
    return -1;
}

int use_pick(int x) {
    int copied = pick(x);
    if (copied < 0) {
        return 0;
    }
    return copied;
}
```

```click
verifying "pick_cases.c";

int pick(int x) {
    ensures result == 18 or result == -1;
} by {
    execute();
    simp();
}

int use_pick(int x) {
    ensures result == 18 or result == 0;
} by {
    execute();
    if result == 0 {
        simp();
    } else {
        have result == 18 by {
            cases (result == 18 or result == -1) {
                simp();
            } {
                have result < 0 by {
                    simp();
                }
                contradiction(result < 0);
            }
        }
        simp();
    }
}
```

```expect
pass
```
