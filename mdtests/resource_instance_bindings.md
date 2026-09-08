# Named resource bindings and symbolic fields

A contract names an exclusive resource instance without adding a ghost C
parameter. Its fields are arbitrary symbolic values, not selected constructors.
This first source regression preserves an opaque resource; opening its memory
body is a separate proof operation.

```c filename=resource_instance_bindings.c
int32 identity(int32 value) {
    return value;
}
```

```click
verifying "resource_instance_bindings.c";

spec enum Mark { Clear, Set }

resource marked_cell() {
    field model: Mark;
    field revision: int32;
}

int32 identity(int32 value) {
    owns cell: marked_cell();
    ensures result == value;
    ensures cell.model == old(cell.model);
    ensures cell.revision == old(cell.revision);
} by {
    execute();
    simp();
}
```

```expect
pass
```
