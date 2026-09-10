# Callback refinement rejects wider unguarded ownership

The named contract owns the cell only while it is active. The concrete function
owns that cell unconditionally, which is more than the interface owns, so it
cannot be used through the narrower named contract.

```c filename=weaker_guarded_callback.c
int32 overly_general_effect(int32 active, int32* cell) {
    return active;
}

int32 apply_guarded_effect(
    int32 (*callback)(int32, int32*),
    int32 active,
    int32* cell
) {
    return callback(active, cell);
}

int32 weaker_guard_caller(int32* cell) {
    return apply_guarded_effect(&overly_general_effect, 1, cell);
}
```

```click
resource maybe_cell(active: int32, cell: int32*) {
    if active != 0 {
        owns cell[0..1];
    }
}

verifying "weaker_guarded_callback.c";

contract int32 GuardedEffect(int32 active, int32* cell) {
    owns maybe_cell(active, cell);
    ensures result == active;
}

int32 overly_general_effect(int32 active, int32* cell) {
    owns cell[0..1];
    ensures result == active;
} by {
    execute();
    simp();
}

int32 apply_guarded_effect(
    int32 (*callback)(int32, int32*),
    int32 active,
    int32* cell
) {
    requires GuardedEffect(callback);
    owns maybe_cell(active, cell);
    ensures result == active;
} by {
    if active != 0 {
        execute();
        simp();
    } else {
        execute();
        simp();
    }
}

int32 weaker_guard_caller(int32* cell) {
    owns maybe_cell(1, cell);
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: function `overly_general_effect` does not satisfy named contract `GuardedEffect`
```
