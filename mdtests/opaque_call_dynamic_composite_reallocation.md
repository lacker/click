# opaque reallocation distinguishes returned projections from the caller frame

An opaque call may return a composite whose allocation and owned range have a
different dynamic size from the consumed composite. Those returned projections
describe the successor allocation; they are not persistent caller views of the
retired input allocation.

```c filename=replace_dynamic_cell.c
struct cell_owner {
    int32 cap;
    int32* data;
};

int32 replace_dynamic_cell(struct cell_owner* owner) {
    int32* old_data;
    int32* new_data;

    old_data = owner->data;
    new_data = malloc(8);
    if (new_data == 0) {
        return 0;
    }
    new_data[0] = 7;
    new_data[1] = 8;
    owner->data = new_data;
    owner->cap = 2;
    free(old_data);
    return 1;
}
```

```c filename=replace_after_dynamic_open.c
struct cell_owner {
    int32 cap;
    int32* data;
};

int32 replace_after_dynamic_open(struct cell_owner* owner) {
    int32 replaced;

    replaced = replace_dynamic_cell(owner);
    return replaced;
}
```

```click
resource allocated_dynamic_cell(owner: struct cell_owner*) {
    owns owner->cap;
    owns owner->data;
    contains allocation(owner->data, owner->cap * 4);
    owns owner->data[0..owner->cap];
    fact owner->cap == 1 or owner->cap == 2;
}

verifying "replace_dynamic_cell.c";
verifying "replace_after_dynamic_open.c";

int32 replace_dynamic_cell(struct cell_owner* owner) {
    consumes allocated_dynamic_cell(owner);
    mutable owner->cap, owner->data, owner->data[0..owner->cap];
    produces allocated_dynamic_cell(owner);

    ensures result == 0 or result == 1;
    ensures result == 0 implies owner->cap == old(owner->cap);
    ensures result == 0 implies owner->data == old(owner->data);
    ensures result == 1 implies owner->cap == 2;
} by {
    unfold(allocated_dynamic_cell(owner));
    execute();
    fold(allocated_dynamic_cell(owner));
    frame();
    simp();
}

int32 replace_after_dynamic_open(struct cell_owner* owner) {
    consumes allocated_dynamic_cell(owner);
    mutable owner->cap, owner->data, owner->data[0..owner->cap];
    produces allocated_dynamic_cell(owner);

    ensures result == 0 or result == 1;
} by {
    open(allocated_dynamic_cell(owner)) {
    }
    execute();
    frame();
    simp();
}
```

```expect
pass
```
