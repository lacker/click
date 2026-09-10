# Callback refinement frames a symbolic owned subrange

Bounds on `index` prove that the concrete callback's one-cell ownership lies
inside the slice transferred by the named contract.  The rest of the slice is
preserved through the concrete transition.

```c filename=symbolic_framed_callback_resource.c
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

void symbolic_framed_resource_caller(
    int32* cells,
    int32 index,
    int32 length
) {
    apply_step(&increment_at, cells, index, length);
}
```

```click
verifying "symbolic_framed_callback_resource.c";

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
    owns state[position..position + 1];
    ensures state[position] == old(state[position]) + 1;
} by {
    execute();
    simp();
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

void symbolic_framed_resource_caller(
    int32* cells,
    int32 index,
    int32 length
) {
    requires 0 <= index;
    requires index < length;
    requires cells[index] < 100;
    owns cells[0..length];
    ensures old(cells[index]) < cells[index];
} by {
    execute();
    simp();
}
```

```expect
pass
```
