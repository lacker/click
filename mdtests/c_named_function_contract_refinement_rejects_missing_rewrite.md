# A refinement certificate that drops its rewrite is rejected

This is the expansion of `c_named_function_contract_refines_rewritten_decrease_guarantee`
with one step deleted: the `rewrite` that turns `Decrease`'s clause about the
new cell value into a comparison about the old one. The kernel no longer
searches recorded equality classes for a rewrite that would decide the clause,
so the proof fails at exactly the step the certificate is missing.

```c filename=rewritten_decrease_step.c
void decrement(int32* state) {
    state[0] -= 1;
}

void apply_step(void (*step)(int32*), int32* cell) {
    step(cell);
}

void rewritten_decrease_caller(int32* cell) {
    apply_step(&decrement, cell);
}
```

```click
verifying "rewritten_decrease_step.c";

contract void Decrease(int32* cell) {
    requires 0 < cell[0];
    requires cell[0] < 100;
    owns cell[0..1];
    ensures cell[0] < old(cell[0]);
}

void decrement(int32* state) {
    requires 0 < state[0];
    owns state[0..1];
    ensures state[0] == old(state[0]) - 1;
} by {
    execute();
    simp();
}

theorem decrement_is_decrease() {
    ensures Decrease(&decrement) by {
        unfold(Decrease);
        intro();
        extract(at(function.entry, loadable(cell[0..1])));
        extract(0 < old(*cell));
        extract(at(function.entry, loadable(cell[0..1])));
        extract(old(*cell) < 100);
        both {
            split();
        } and {
            intro();
            extract(loadable(cell[0..1]));
            extract(*cell == (old(*cell) - 1));
            both {
                assumption();
            } and {
                apply(int32_positive_predecessor_strictly_decreases(old(*cell))) using {
                    0 < old(*cell);
                }
            }
        }
    }
}

void apply_step(void (*step)(int32*), int32* cell) {
    requires Decrease(step);
    requires 0 < cell[0];
    requires cell[0] < 100;
    owns cell[0..1];
    ensures cell[0] < old(cell[0]);
} by {
    execute();
    simp();
}

void rewritten_decrease_caller(int32* cell) {
    requires 0 < cell[0];
    requires cell[0] < 100;
    owns cell[0..1];
    ensures cell[0] < old(cell[0]);
} by {
    apply(decrement_is_decrease());
    execute();
    simp();
}
```

```expect
fail: `decrement_is_decrease.ensures_0`: contract-refinement proof does not establish `Decrease(&decrement)`
```
