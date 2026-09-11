# A refinement certificate that names the wrong arm is rejected

This is the expansion of `c_named_function_contract_refines_disjunctive_clause`
with `right()` replaced by `left()`. `increment` grows the cell, so only the
right arm of `Stable`'s disjunctive clause holds. The kernel chooses no arm on
the proof's behalf, so naming the other one fails.

```c filename=disjunctive_step.c
void increment(int32* state) {
    state[0] += 1;
}

void apply_step(void (*step)(int32*), int32* cell) {
    step(cell);
}

void disjunctive_clause_caller(int32* cell) {
    apply_step(&increment, cell);
}
```

```click
verifying "disjunctive_step.c";

contract void Stable(int32* cell) {
    requires cell[0] < 100;
    owns cell[0..1];
    ensures cell[0] == old(cell[0]) or old(cell[0]) < cell[0];
}

void increment(int32* state) {
    requires state[0] < 1000;
    owns state[0..1];
    ensures state[0] == old(state[0]) + 1;
} by {
    execute();
    simp();
}

theorem increment_is_stable() {
    ensures Stable(&increment) by {
        unfold(Stable);
        intro();
        extract(at(function.entry, loadable(cell[0..1])));
        extract(old(*cell) < 100);
        both {
            both {
                assumption();
            } and {
                apply(int32_lt_transitive(old(*cell), 100, 1000)) using {
                    old(*cell) < 100;
                }
            }
        } and {
            intro();
            extract(loadable(cell[0..1]));
            extract(*cell == (old(*cell) + 1));
            both {
                assumption();
            } and {
                have old(*cell) < *cell by {
                    rewrite(*cell == (old(*cell) + 1));
                    apply(int32_increment_strictly_increases(old(*cell), 100)) using {
                        old(*cell) < 100;
                    }
                }
                left();
            }
        }
    }
}

void apply_step(void (*step)(int32*), int32* cell) {
    requires Stable(step);
    requires cell[0] < 100;
    owns cell[0..1];
    ensures cell[0] == old(cell[0]) or old(cell[0]) < cell[0];
} by {
    execute();
    simp();
}

void disjunctive_clause_caller(int32* cell) {
    requires cell[0] < 100;
    owns cell[0..1];
    ensures cell[0] == old(cell[0]) or old(cell[0]) < cell[0];
} by {
    apply(increment_is_stable());
    execute();
    simp();
}
```

```expect
fail: `left` requires its selected disjunct as an exact fact
```
