# A concrete state transformer may not promise less than its named contract

The implementation promises only that the cell is unchanged or increments.
That is not enough to form a callback value whose named contract promises
strict progress, even though this particular C body increments the cell.

```c filename=weak_stateful_step.c
void maybe_progress(int32* state) {
    state[0] += 1;
}

void apply_step(void (*step)(int32*), int32* cell) {
    step(cell);
}

void weak_stateful_refinement_caller(int32* cell) {
    apply_step(&maybe_progress, cell);
}
```

```click
verifying "weak_stateful_step.c";

contract void Progress(int32* cell) {
    requires cell[0] < 100;
    owns cell[0..1];
    mutable cell[0..1];
    ensures old(cell[0]) < cell[0];
}

void maybe_progress(int32* state) {
    requires state[0] < 100;
    owns state[0..1];
    mutable state[0..1];
    ensures state[0] == old(state[0]) + 1 or state[0] == old(state[0]);
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

void weak_stateful_refinement_caller(int32* cell) {
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
fail: function `maybe_progress` does not satisfy named contract `Progress`
```
