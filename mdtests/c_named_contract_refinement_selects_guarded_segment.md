# Callback refinement covers each guarded segment from the matching one

The named contract owns two conditional cells whose guards are opposites, so
its mutable footprint has two guarded segments. The callback's own guarded
segment must be covered by the contract segment whose guard is active here,
not by the first one declared: the idle segment's guard is refuted by the
contract's precondition. The callback's idle segment is likewise refuted, so
it demands no coverage at all.

```c filename=guarded_selection_callback.c
int32 keep_selected(int32 active, int32* on_cell, int32* off_cell) {
    return active;
}

int32 apply_selected(
    int32 (*callback)(int32, int32*, int32*),
    int32 active,
    int32* on_cell,
    int32* off_cell
) {
    return callback(active, on_cell, off_cell);
}

int32 selected_caller(int32* on_cell, int32* off_cell) {
    return apply_selected(&keep_selected, 1, on_cell, off_cell);
}
```

```click
resource active_cell(active: int32, cell: int32*) {
    if active != 0 {
        owns cell[0..1];
    }
}

resource idle_cell(active: int32, cell: int32*) {
    if active == 0 {
        owns cell[0..1];
    }
}

verifying "guarded_selection_callback.c";

contract int32 KeepSelected(int32 active, int32* on_cell, int32* off_cell) {
    requires active != 0;
    owns idle_cell(active, off_cell);
    owns active_cell(active, on_cell);
    ensures result == active;
}

int32 keep_selected(int32 active, int32* on_cell, int32* off_cell) {
    owns idle_cell(active, off_cell);
    owns active_cell(active, on_cell);
    ensures result == active;
} by {
    execute();
    simp();
}

int32 apply_selected(
    int32 (*callback)(int32, int32*, int32*),
    int32 active,
    int32* on_cell,
    int32* off_cell
) {
    requires KeepSelected(callback);
    requires active != 0;
    owns idle_cell(active, off_cell);
    owns active_cell(active, on_cell);
    ensures result == active;
} by {
    execute();
    simp();
}

int32 selected_caller(int32* on_cell, int32* off_cell) {
    owns idle_cell(1, off_cell);
    owns active_cell(1, on_cell);
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
