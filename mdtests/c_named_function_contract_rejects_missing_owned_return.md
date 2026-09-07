# A callback must return the ownership its named contract promises

Both interfaces can receive the cell, but the concrete callback consumes its
ownership instead of returning it.  It therefore cannot form a callback value
whose named contract preserves ownership for the caller.

```c filename=missing_callback_resource_return.c
void consume_cell(int32* state) {
}

void apply_step(void (*step)(int32*), int32* cell) {
    step(cell);
}

void missing_resource_return_caller(int32* cell) {
    apply_step(&consume_cell, cell);
}
```

```click
verifying "missing_callback_resource_return.c";

contract void Preserve(int32* cell) {
    owns cell[0..1];
}

void consume_cell(int32* state) {
    consumes state[0..1];
}

void apply_step(void (*step)(int32*), int32* cell) {
    requires Preserve(step);
    owns cell[0..1];
} by {
    execute();
    simp();
}

void missing_resource_return_caller(int32* cell) {
    owns cell[0..1];
} by {
    execute();
}
```

```expect
fail: function `consume_cell` does not satisfy named contract `Preserve`
```
