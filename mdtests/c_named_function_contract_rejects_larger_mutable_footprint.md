# A callback may not mutate more memory than its named contract permits

The concrete function happens to write only the first cell, but its public
contract permits either cell to change.  That larger effect cannot form a
callback value whose named contract permits mutation of only the first cell.

```c filename=larger_callback_footprint.c
void broadly_mutable(int32* state) {
    state[0] += 1;
}

void apply_step(void (*step)(int32*), int32* cells) {
    step(cells);
}

void larger_footprint_caller(int32* cells) {
    apply_step(&broadly_mutable, cells);
}
```

```click
verifying "larger_callback_footprint.c";

contract void Progress(int32* cells) {
    requires cells[0] < 100;
    owns cells[0..2];
    mutable cells[0..1];
    ensures old(cells[0]) < cells[0];
}

void broadly_mutable(int32* state) {
    requires state[0] < 100;
    owns state[0..2];
    mutable state[0..2];
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
    mutable cells[0..1];
    ensures old(cells[0]) < cells[0];
} by {
    execute();
    frame();
    simp();
}

void larger_footprint_caller(int32* cells) {
    requires cells[0] < 100;
    owns cells[0..2];
    mutable cells[0..1];
    ensures old(cells[0]) < cells[0];
} by {
    execute();
    frame();
    simp();
}
```

```expect
fail: function `broadly_mutable` does not satisfy named contract `Progress`
```
