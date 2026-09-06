# A callback may mutate less memory than its named contract permits

The named contract permits either cell to change, while the concrete callback
changes only the first.  Resource transfer remains exact: both interfaces own
and return the entire two-cell state.

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
    mutable cells[0..2];
    ensures old(cells[0]) < cells[0];
}

void increment_first(int32* state) {
    requires state[0] < 100;
    owns state[0..2];
    mutable state[0..1];
    ensures state[0] == old(state[0]) + 1;
} by {
    execute();
    frame();
    simp();
}

void apply_step(void (*step)(int32*), int32* cells) {
    requires Progress(step);
    requires cells[0] < 100;
    owns cells[0..2];
    mutable cells[0..2];
    ensures old(cells[0]) < cells[0];
} by {
    execute();
    frame();
    simp();
}

void smaller_footprint_caller(int32* cells) {
    requires cells[0] < 100;
    owns cells[0..2];
    mutable cells[0..2];
    ensures old(cells[0]) < cells[0];
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
