# A named precondition can establish a mutable guard

The named contract is callable only while its conditional cell is active. In
that domain the named guarded footprint is always enabled, so a concrete
function may state the same range as unconditionally mutable.

```c filename=precondition_guarded_callback.c
int32 active_effect(int32 active, int32* cell) {
    return active;
}

int32 apply_active_effect(
    int32 (*callback)(int32, int32*),
    int32 active,
    int32* cell
) {
    return callback(active, cell);
}

int32 active_effect_caller(int32* cell) {
    return apply_active_effect(&active_effect, 1, cell);
}
```

```click
resource maybe_cell(active: int32, cell: int32*) {
    if active != 0 {
        owns cell[0..1];
    }
}

verifying "precondition_guarded_callback.c";

contract int32 ActiveEffect(int32 active, int32* cell) {
    requires active != 0;
    owns maybe_cell(active, cell);
    ensures result == active;
}

int32 active_effect(int32 active, int32* cell) {
    requires active != 0;
    owns maybe_cell(active, cell);
    mutable cell[0..1];
    ensures result == active;
} by {
    execute();
    frame();
    simp();
}

int32 apply_active_effect(
    int32 (*callback)(int32, int32*),
    int32 active,
    int32* cell
) {
    requires ActiveEffect(callback);
    requires active != 0;
    owns maybe_cell(active, cell);
    ensures result == active;
} by {
    execute();
    simp();
}

int32 active_effect_caller(int32* cell) {
    owns maybe_cell(1, cell);
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
