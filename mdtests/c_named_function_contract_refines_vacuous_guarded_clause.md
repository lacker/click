# A guarded contract clause may be refined by refuting its guard

`GuardedProgress` promises to leave a negative cell alone, and separately
requires that the cell is not negative. The concrete `increment` always adds
one, so it refines the guarded clause only because the guard is refuted by the
named contract's own precondition. Refinement checking must decide that from
the assumed precondition, without assuming the guard and re-proving the
consequent.

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
    execute();
    simp();
}
```

```expect
pass
```
