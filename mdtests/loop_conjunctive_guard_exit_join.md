# The joined exit says which conjunct failed

The loop rule joins the guard's exit paths, and the join is not only their
common facts: it also carries the disjunction of what each path states alone.
For `while (a != 0 && p[0] != 0)` that is `a == 0 or p[0] == 0`, which is what
the C actually knows after the loop.

The disjunction is written in that form rather than as
`a == 0 or (a != 0 and p[0] == 0)`. A conjunct another exit path contradicts is
dropped, which only weakens that disjunct and so keeps the disjunction true,
and it leaves a fact a proof can name.

Here the proof needs it: the `then` arm has taken the branch where `a` is
nonzero, so the first disjunct is refuted and the returned `p[0]` must be zero.
`cases` splits on the exported disjunction and closes the refuted side by
contradiction.

The loop terminates because the body zeroes `a`, so `a` is the measure. Its
decrease obligation is `0 < a` at the head, which the first guard conjunct
gives only as `a != 0`; the arithmetic members are affine, so the preservation
body turns the disequality into `a > 0` by ruling out `a == 0` against that
conjunct before the step runs.

```c filename=loop_conjunctive_guard_exit_join.c
int32 uses_exit_disjunction(int32 a, int32 *p) {
    while (a != 0 && p[0] != 0) {
        a = 0;
    }
    if (a != 0)
        return p[0];
    return 0;
}
```

```click
verifying "loop_conjunctive_guard_exit_join.c";

int32 uses_exit_disjunction(int32 a, int32* p) {
    requires a >= 0;
    requires a <= 10;
    views p[0..1];
    ensures result == 0;
} by {
    loop {
        decreases a;
        invariant a >= 0;
        invariant a <= 10;

        initialize by simp;
        preserve by {
            have a > 0 by {
                if a > 0 {
                    assumption();
                } else {
                    have a == 0 by {
                        apply(int32_ge_and_not_gt_implies_eq(a, 0)) using {
                            a >= 0;
                            not (a > 0);
                        }
                    }
                    contradiction(a == 0);
                }
            }
            step();
            close_invariants by {
                simp();
            }
        }
    }
    branch {
        then {
            have p[0] == 0 by {
                cases(a == 0 or p[0] == 0) {
                    have a == 0 by {
                        assumption();
                    }
                    contradiction(a == 0);
                } {
                    assumption();
                }
            }
            step();
            simp();
        }
        else {}
    }
    step();
    simp();
}
```

```expect
pass
```
