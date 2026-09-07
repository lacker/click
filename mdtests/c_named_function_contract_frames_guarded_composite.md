# Callback refinement frames conditionally mutable composites

The named contract preserves two conditional cells. The concrete callback
needs and returns only the first, so the second remains in the resource frame.
Its guarded mutable segment also remains an upper bound rather than becoming a
mandatory concrete effect.

```c filename=framed_guarded_callback.c
int32 keep_first_guarded(int32 active, int32* first, int32* spare) {
    return active;
}

int32 apply_guarded_pair(
    int32 (*callback)(int32, int32*, int32*),
    int32 active,
    int32* first,
    int32* spare
) {
    return callback(active, first, spare);
}

int32 guarded_pair_caller(int32* first, int32* spare) {
    return apply_guarded_pair(&keep_first_guarded, 1, first, spare);
}
```

```click
resource maybe_cell(active: int32, cell: int32*) {
    if active != 0 {
        owns cell[0..1];
    }
}

verifying "framed_guarded_callback.c";

contract int32 PreserveGuardedPair(
    int32 active,
    int32* first,
    int32* spare
) {
    owns maybe_cell(active, first);
    owns maybe_cell(active, spare);
    ensures result == active;
}

int32 keep_first_guarded(int32 active, int32* first, int32* spare) {
    owns maybe_cell(active, first);
    ensures result == active;
} by {
    execute();
    simp();
}

int32 apply_guarded_pair(
    int32 (*callback)(int32, int32*, int32*),
    int32 active,
    int32* first,
    int32* spare
) {
    requires PreserveGuardedPair(callback);
    owns maybe_cell(active, first);
    owns maybe_cell(active, spare);
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

int32 guarded_pair_caller(int32* first, int32* spare) {
    owns maybe_cell(1, first);
    owns maybe_cell(1, spare);
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
