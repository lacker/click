# the smart closer splits a conjunction chain before whole-goal search

`count_up` keeps `0 <= i and i <= n and run == i`. The body establishes only
the ranking inequalities, so the back-edge bundle is a right-nested chain of
five conjuncts, and each of the first three needs its own short derivation
from the body's assignments.

`close_invariants()` must split the chain and close each conjunct, rather than
first running the premise-selecting derivation, the indexed goal-equality
rewrite, and the other whole-goal strategies over the complete chain and then
again over every suffix of it as the structural closure descends. Those
strategies still run on each conjunct, and still run on the whole goal when
the split misses, so the closer proves the same goals, but a chain of `n`
conjuncts now costs work linear in `n` instead of quadratic.

```c filename=close_invariants_splits_a_conjunction_chain_first.c
int32 count_up(int32 n) {
    int32 i = 0;
    int32 run = 0;

    while (i < n) {
        run = run + 1;
        i = i + 1;
    }
    return run;
}
```

```click
verifying "close_invariants_splits_a_conjunction_chain_first.c";

int32 count_up(int32 n) {
    requires 0 <= n;
    ensures result == n;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n and run == i;

        initialize by simp;
        preserve by {
            mark iteration;
            have 0 <= at(iteration, i) by { simp(); }
            have run < n by { simp(); }
            step();
            step();
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
    step();
    simp();
}
```

```expect
pass
```
