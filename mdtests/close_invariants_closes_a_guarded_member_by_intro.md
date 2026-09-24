# the smart closer introduces a guarded member's guard

`count_run` counts how far `i` has advanced past `2`. The third invariant says
so with `2 + run == i`, and `2 + run` is an `int32` addition, so the back-edge
bundle states that member under its definedness guard:
`defined(2 + run) implies ...`. The ranking members follow it, so on the
`else` arm the bundle is a conjunction whose first conjunct is that
implication.

Every leaf is already a fact: the body states the disjunction with `right()`
and both ranking inequalities with `arithmetic()`. The closing proof is
`both { intro(); assumption(); } and { split(); }`, and `close_invariants()`
must find it by splitting the bundle and closing each conjunct with the
direct logical steps, before the premise-selecting and rewriting strategies
run over the whole bundle. Before that, this arm fell through to the indexed
goal-equality rewrite and the structural derivation, and on the arena
example the same shape crossed the smart tactic's time limit.

```c filename=close_invariants_closes_a_guarded_member_by_intro.c
int32 count_run(int32 n) {
    int32 i = 0;
    int32 run = 0;

    while (i < n) {
        if (i < 2) {
            run = 0;
        } else {
            run = run + 1;
        }
        i = i + 1;
    }
    return run;
}
```

```click
verifying "close_invariants_closes_a_guarded_member_by_intro.c";

int32 count_run(int32 n) {
    requires 0 <= n;
    ensures 0 <= result;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        invariant 0 <= run and run <= i;
        invariant (i <= 2 and run == 0) or (2 <= i and 2 + run == i);

        initialize by simp;
        preserve by {
            mark iteration;
            if i < 2 {
                branch {
                    then { step(); }
                    else { contradiction(not (i < 2)); }
                }
                step();
                have 0 <= i and i <= n by { simp(); }
                have 0 <= run and run <= i by { simp(); }
                have i <= 2 and run == 0 by { simp(); }
                have (i <= 2 and run == 0) or (2 <= i and 2 + run == i) by { left(); }
                have 0 <= at(iteration, i) by { simp(); }
                have 0 <= n by { simp(); }
                have 0 <= n - at(iteration, i) - 1 by {
                    arithmetic() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, n);
                        0 <= n;
                    }
                }
                have n - at(iteration, i) - 1 < n - at(iteration, i) by {
                    arithmetic() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, n);
                        0 <= n;
                    }
                }
                close_invariants();
            } else {
                have 2 <= i by { arithmetic() using { not (i < 2); } }
                have 2 + run == i by {
                    cases((i <= 2 and run == 0) or (2 <= i and 2 + run == i)) {
                        extract(i <= 2);
                        extract(run == 0);
                        have i == 2 by {
                            apply(int32_le_and_not_lt_implies_eq(i, 2)) using {
                                i <= 2;
                                not (i < 2);
                            }
                            assumption();
                        }
                        rewrite(run == 0);
                        rewrite(i == 2);
                        normalize() using { i <= 2; };
                    } {
                        extract(2 + run == i);
                        assumption();
                    }
                }
                have run < n by {
                    arithmetic() using {
                        run <= i;
                        i < n;
                    }
                }
                branch {
                    then { contradiction(i < 2); }
                    else { step(); }
                }
                step();
                have 0 <= i and i <= n by { simp(); }
                have 0 <= run and run <= i by { simp(); }
                have 2 <= i and 2 + run == i by { simp(); }
                have (i <= 2 and run == 0) or (2 <= i and 2 + run == i) by { right(); }
                have 0 <= at(iteration, i) by { simp(); }
                have 0 <= n by { simp(); }
                have 0 <= n - at(iteration, i) - 1 by {
                    arithmetic() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, n);
                        0 <= n;
                    }
                }
                have n - at(iteration, i) - 1 < n - at(iteration, i) by {
                    arithmetic() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, n);
                        0 <= n;
                    }
                }
                close_invariants();
            }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
