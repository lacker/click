# Callback refinement frames ownership the concrete function does not need

The named contract transfers two owned cells.  The concrete callback needs
and returns only the first, so the second cell remains as a frame around the
concrete transition.  No extra contract syntax is required.

```c filename=framed_callback_resource.c
void increment_first(int32* state) {
    state[0] += 1;
}

void apply_step(void (*step)(int32*), int32* cells) {
    step(cells);
}

void framed_resource_caller(int32* cells) {
    apply_step(&increment_first, cells);
}
```

```click
verifying "framed_callback_resource.c";

contract void Progress(int32* cells) {
    requires cells[0] < 100;
    owns cells[0..2];
    ensures old(cells[0]) < cells[0];
}

void increment_first(int32* state) {
    requires state[0] < 100;
    owns state[0..1];
    ensures state[0] == old(state[0]) + 1;
} by {
    execute();
    simp();
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

void framed_resource_caller(int32* cells) {
    requires cells[0] < 100;
    owns cells[0..2];
    ensures old(cells[0]) < cells[0];
} by {
    execute();
    simp();
}
```

```expect
pass
```
