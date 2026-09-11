# A guarded contract clause is not refined when its guard stands

The same `increment` and the same guarded clause as
`c_named_function_contract_refines_vacuous_guarded_clause`, except that
`GuardedProgress` no longer requires a non-negative cell. Its guard is now
possible, and a cell that starts negative is incremented rather than left
alone, so the clause is not refined. Refinement must reject the callback
instead of assuming the guard and proving the consequent under it.

```c filename=unrefuted_guarded_step.c
void increment(int32* state) {
    state[0] += 1;
}

void apply_step(void (*step)(int32*), int32* cell) {
    step(cell);
}

void unrefuted_guard_caller(int32* cell) {
    apply_step(&increment, cell);
}
```

```click
verifying "unrefuted_guarded_step.c";

contract void GuardedProgress(int32* cell) {
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

void apply_step(void (*step)(int32*), int32* cell) {
    requires GuardedProgress(step);
    requires cell[0] < 100;
    owns cell[0..1];
    ensures old(cell[0]) < cell[0];
} by {
    execute();
    simp();
}

void unrefuted_guard_caller(int32* cell) {
    requires cell[0] < 100;
    owns cell[0..1];
    ensures old(cell[0]) < cell[0];
} by {
    execute();
    simp();
}
```

```expect
fail: function `increment` does not satisfy named contract `GuardedProgress`
```
