# A proof `cases` after a C branch expands

`pick` returns `18` or `-1`, and `use_pick` returns `0` for a negative
result and the result otherwise. The caller proof steps over the call and
splits with `branch` at the C `if`: the `copied < 0` arm steps to exit with
`step_until(function.exit)`, and the empty `else` arm falls through to the
continuation, which steps to exit and proves `result == 18` with a `cases` on
`pick`'s disjunctive postcondition, closing the `-1` case by contradiction.

Claim expansion once synthesized the proof cases across all outcomes at once
and refused with "distinct certified paths have no surface branch condition",
although verification and `click audit` accepted the proof. Expansion places
the proof cases on the path that reaches them, after the C branch. The
expansion regression in `src/surface/tests/expansion_tests.rs` expands this
claim and re-verifies the rewrite.

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
}

int use_pick(int x) {
    ensures result == 18 or result == 0;
} by {
    step();
    step();
    step();
    branch {
        true => {
            step_until(function.exit);
        }
        false => {
        }
    }
    step_until(function.exit);
    have result == 18 by {
        cases {
            result == 18 => {
                close();
            }
            result == -1 => {
                have result < 0 by {
                    close();
                }
                contradiction(result < 0);
            }
        }
    }
}
```

```expect
pass
```
