# scoped composite views close before opaque reallocation

Opening an owned composite temporarily exposes its allocation and memory body.
After the scope closes, an opaque verified call may replace that body and retire
the old allocation. View cores projected from the callee's newly ensured
ownership are not independent caller views of the retired input allocation.

```c filename=replace_allocated_cell.c
struct cell_owner {
    int32* data;
};

int32 replace_allocated_cell(struct cell_owner* owner) {
    int32* old_data;
    int32* new_data;

    old_data = owner->data;
    new_data = malloc(4);
    if (new_data == 0) {
        return 0;
    }
    new_data[0] = 7;
    owner->data = new_data;
    free(old_data);
    return 1;
}
```

```c filename=replace_after_scoped_open.c
struct cell_owner {
    int32* data;
};

int32 replace_after_scoped_open(struct cell_owner* owner) {
    int32 replaced;

    replaced = replace_allocated_cell(owner);
    return replaced;
}
```

```click
resource allocated_cell(owner: struct cell_owner*) {
    owns owner->data;
    contains allocation(owner->data, 4);
    owns owner->data[0..1];
}

verifying "replace_allocated_cell.c";
verifying "replace_after_scoped_open.c";

int32 replace_allocated_cell(struct cell_owner* owner) {
    consumes allocated_cell(owner);
    mutable owner->data, owner->data[0..1];
    produces allocated_cell(owner);

    ensures result == 0 or result == 1;
    ensures result == 0 implies owner->data == old(owner->data);
} by {
    unfold(allocated_cell(owner));
    execute();
    fold(allocated_cell(owner));
    frame();
    simp();
}

int32 replace_after_scoped_open(struct cell_owner* owner) {
    consumes allocated_cell(owner);
    mutable owner->data, owner->data[0..1];
    produces allocated_cell(owner);

    ensures result == 0 or result == 1;
} by {
    open(allocated_cell(owner)) {
    }
    execute();
    simp();
}
```

```expect
pass
```
