# A concrete state transformer may refine a named contract

A callback whose verified contract describes an exact update can satisfy a
named contract that promises only progress.  Both contracts use the same
resource transfer and mutable footprint, while their parameter names are
independent binders.

```c filename=stateful_refining_step.c
void increment(int32* state) {
    state[0] += 1;
}

void apply_step(void (*step)(int32*), int32* cell) {
    step(cell);
}

void stateful_refinement_caller(int32* cell) {
    apply_step(&increment, cell);
}
```

```click
verifying "stateful_refining_step.c";

contract void Progress(int32* cell) {
    requires cell[0] < 100;
    owns cell[0..1];
    mutable cell[0..1];
    ensures old(cell[0]) < cell[0];
}

void increment(int32* state) {
    requires state[0] < 1000;
    owns state[0..1];
    mutable state[0..1];
    ensures state[0] == old(state[0]) + 1;
} by {
    execute();
    frame();
    simp();
}

void apply_step(void (*step)(int32*), int32* cell) {
    requires Progress(step);
    requires cell[0] < 100;
    owns cell[0..1];
    mutable cell[0..1];
    ensures old(cell[0]) < cell[0];
} by {
    execute();
    frame();
    simp();
}

void stateful_refinement_caller(int32* cell) {
    requires cell[0] < 100;
    owns cell[0..1];
    mutable cell[0..1];
    ensures old(cell[0]) < cell[0];
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
