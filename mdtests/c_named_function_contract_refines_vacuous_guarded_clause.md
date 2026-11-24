# A guarded contract clause may be refined by refuting its guard

`GuardedProgress` promises to leave a negative cell alone, and separately
requires that the cell is not negative. The concrete `increment` always adds
one, so it refines the guarded clause only because the guard is refuted by the
named contract's own precondition. The refutation is spelled in the refinement
theorem — `have not (...)`, `intro`, `contradiction` — rather than decided
inside contract formation.

```c filename=vacuous_guarded_step.c
void increment(int32* state) {
    state[0] += 1;
}

void apply_step(void (*step)(int32*), int32* cell) {
    step(cell);
}

void vacuous_guard_caller(int32* cell) {
    apply_step(&increment, cell);
}
```

```click
verifying "vacuous_guarded_step.c";

contract void GuardedProgress(int32* cell) {
    requires 0 <= cell[0];
    requires cell[0] < 100;
    owns cell[0..1];
    ensures old(cell[0]) < 0 implies cell[0] == old(cell[0]);
    ensures old(cell[0]) < cell[0];
}

void increment(int32* state) {
    requires state[0] < 1000;
    owns state[0..1];
    ensures to_integer(state[0]) == to_integer(old(state[0]) + 1);
}

theorem increment_is_guarded_progress() {
    ensures GuardedProgress(&increment) by {
        unfold(GuardedProgress(&increment));
        intro();
        all {
            old(cell[0]) < 1000 => {
                have 100 <= 1000 by close();
                apply(click::integer::int32_less_than_less_equal_transitive(old(cell[0]), 100, 1000));
            }
            (
                to_integer(old(cell[0])) + 1 <= 2147483647 and
                to_integer(old(cell[0])) + 1 >= -2147483648 and
                to_integer(cell[0]) == to_integer(old(cell[0]) + 1)
                implies (old(cell[0]) < 0 implies cell[0] == old(cell[0])) and old(cell[0]) < cell[0]
            ) => {
                intro();
                all {
                    (old(cell[0]) < 0 implies cell[0] == old(cell[0])) => {
                        have not (old(cell[0]) < 0) by {
                            close() using { 0 <= old(cell[0]); };
                        }
                        intro();
                        contradiction(not (old(cell[0]) < 0));
                    }
                    old(cell[0]) < cell[0] => {
                        close();
                    }
                }
            }
        }
    }
}

void apply_step(void (*step)(int32*), int32* cell) {
    requires GuardedProgress(step);
    requires 0 <= cell[0];
    requires cell[0] < 100;
    owns cell[0..1];
    ensures old(cell[0]) < cell[0];
}

void vacuous_guard_caller(int32* cell) {
    requires 0 <= cell[0];
    requires cell[0] < 100;
    owns cell[0..1];
    ensures old(cell[0]) < cell[0];
} by {
    apply(increment_is_guarded_progress());
}
```

```expect
pass
```
