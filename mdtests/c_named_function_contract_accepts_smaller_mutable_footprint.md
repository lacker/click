# A callback may own less memory than its named contract permits

The named contract owns both cells, while the concrete callback views the pair
and owns only the first. Resource transfer remains exact: both interfaces
return the entire two-cell state.

Behavioral refinement of a named contract is an explicit theorem: the kernel
checks that the two interfaces have compatible shape, and the clause-level
implication is proved by ordinary tactics.

```c filename=smaller_callback_footprint.c
void increment_first(int32* state) {
    state[0] += 1;
}

void apply_step(void (*step)(int32*), int32* cells) {
    step(cells);
}

void smaller_footprint_caller(int32* cells) {
    apply_step(&increment_first, cells);
}
```

```click
verifying "smaller_callback_footprint.c";

contract void Progress(int32* cells) {
    requires cells[0] < 100;
    owns cells[0..2];
    ensures old(cells[0]) < cells[0];
}

void increment_first(int32* state) {
    requires state[0] < 100;
    views state[0..2];
    owns state[0..1];
    ensures state[0] == old(state[0]) + 1;
} by {
    execute();
    simp();
}

theorem increment_first_is_progress() {
    ensures Progress(&increment_first) by {
        unfold(Progress);
        simp();
    }
}

void apply_step(void (*step)(int32*), int32* cells) {
    requires Progress(step);
    requires cells[0] < 100;
    owns cells[0..2];
    ensures old(cells[0]) < cells[0];
} by {
    execute();
    simp();
}

void smaller_footprint_caller(int32* cells) {
    requires cells[0] < 100;
    owns cells[0..2];
    ensures old(cells[0]) < cells[0];
} by {
    apply(increment_first_is_progress());
    execute();
    simp();
}
```

```expect
pass
```
