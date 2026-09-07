# Callback refinement can borrow a conditionally mutable composite

The named contract permits mutation when the cell is active. The concrete
callback only borrows the folded resource and has no mutable footprint, which
is a valid refinement. Ownership remains available after the indirect call.

```c filename=borrowed_guarded_callback.c
int32 inspect_guarded(int32 active, int32* cell) {
    return active;
}

int32 apply_guarded_inspect(
    int32 (*callback)(int32, int32*),
    int32 active,
    int32* cell
) {
    return callback(active, cell);
}

int32 guarded_borrow_caller(int32* cell) {
    return apply_guarded_inspect(&inspect_guarded, 1, cell);
}
```

```click
resource maybe_cell(active: int32, cell: int32*) {
    if active != 0 {
        owns cell[0..1];
    }
}

verifying "borrowed_guarded_callback.c";

contract int32 InspectGuarded(int32 active, int32* cell) {
    owns maybe_cell(active, cell);
    ensures result == active;
}

int32 inspect_guarded(int32 active, int32* cell) {
    views maybe_cell(active, cell);
    ensures result == active;
} by {
    execute();
    simp();
}

int32 apply_guarded_inspect(
    int32 (*callback)(int32, int32*),
    int32 active,
    int32* cell
) {
    requires InspectGuarded(callback);
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

int32 guarded_borrow_caller(int32* cell) {
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
