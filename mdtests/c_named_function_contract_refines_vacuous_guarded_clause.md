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
    ensures state[0] == old(state[0]) + 1;
} by {
    execute();
    simp();
}

theorem increment_is_guarded_progress() {
    ensures GuardedProgress(&increment) by {
        unfold(GuardedProgress);
        intro();
        extract(at(function.entry, loadable(cell[0..1])));
        extract(0 <= old(cell[0]));
        extract(old(cell[0]) < 100);
        both {
            both {
                assumption();
            } and {
                apply(int32_lt_transitive(old(cell[0]), 100, 1000)) using {
                    old(cell[0]) < 100;
                }
            }
        } and {
            intro();
            extract(loadable(cell[0..1]));
            extract(cell[0] == old(cell[0]) + 1);
            both {
                both {
                    both {
                        assumption();
                    } and {
                        have not (old(cell[0]) < 0) by {
                            arithmetic() using {
                                0 <= old(cell[0]);
                            }
                        }
                        intro();
                        contradiction(not (old(cell[0]) < 0));
                    }
                } and {
                    assumption();
                }
            } and {
                rewrite(cell[0] == old(cell[0]) + 1);
                apply(int32_increment_strictly_increases(old(cell[0]), 100)) using {
                    old(cell[0]) < 100;
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
} by {
    execute();
    simp();
}

void vacuous_guard_caller(int32* cell) {
    requires 0 <= cell[0];
    requires cell[0] < 100;
    owns cell[0..1];
    ensures old(cell[0]) < cell[0];
} by {
    apply(increment_is_guarded_progress());
    execute();
    simp();
}
```

```expect
pass
```
