# Callback footprint refinement proves symbolic subrange containment

The named contract permits mutation anywhere in a symbolic slice.  Bounds on
`index` prove that the concrete callback's one-cell footprint lies inside that
slice.

Behavioral refinement of a named contract is an explicit theorem: the kernel
checks that the two interfaces have compatible shape, and the clause-level
implication is proved by ordinary tactics.

```c filename=symbolic_callback_footprint.c
void increment_at(int32* state, int32 position, int32 count) {
    state[position] += 1;
}

void apply_step(
    void (*step)(int32*, int32, int32),
    int32* cells,
    int32 index,
    int32 length
) {
    step(cells, index, length);
}

void symbolic_footprint_caller(int32* cells, int32 index, int32 length) {
    apply_step(&increment_at, cells, index, length);
}
```

```click
verifying "symbolic_callback_footprint.c";

contract void SliceStep(int32* cells, int32 index, int32 length) {
    requires 0 <= index;
    requires index < length;
    requires cells[index] < 100;
    owns cells[0..length];
    ensures old(cells[index]) < cells[index];
}

void increment_at(int32* state, int32 position, int32 count) {
    requires 0 <= position;
    requires position < count;
    requires state[position] < 100;
    views state[0..count];
    owns state[position..position + 1];
    ensures state[position] == old(state[position]) + 1;
} by {
    execute();
    simp();
}

theorem increment_at_is_slice_step() {
    ensures SliceStep(&increment_at) by {
        unfold(SliceStep);
        simp();
    }
}

void apply_step(
    void (*step)(int32*, int32, int32),
    int32* cells,
    int32 index,
    int32 length
) {
    requires SliceStep(step);
    requires 0 <= index;
    requires index < length;
    requires cells[index] < 100;
    owns cells[0..length];
    ensures old(cells[index]) < cells[index];
} by {
    execute();
    simp();
}

void symbolic_footprint_caller(int32* cells, int32 index, int32 length) {
    requires 0 <= index;
    requires index < length;
    requires cells[index] < 100;
    owns cells[0..length];
    ensures old(cells[index]) < cells[index];
} by {
    apply(increment_at_is_slice_step());
    execute();
    simp();
}
```

```expect
pass
```
