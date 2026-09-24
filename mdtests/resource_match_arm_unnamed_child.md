# A match arm may own an unnamed declared resource

A match arm owns a field-free declared resource with the same unnamed
`owns cell_value(cell);` spelling a body uses at top level. The resource
stays folded inside the arm, so unfolding the parent exposes it as an owned,
folded `cell_value(cell)`, and folding the parent consumes it again. No child
name, field, or model is needed for a resource that carries no model.

`set` unfolds the matched parent and then the unnamed resource, stores
through its cell, and folds both back before the function returns.

```c filename=resource_match_arm_unnamed_child.c
struct cell { int32 value; };

void set(struct cell* cell) {
    cell->value = 3;
}
```

```click
spec enum Mode { Held, Empty }

resource cell_value(cell: struct cell*) {
    owns cell->value;
}

resource maybe_cell(cell: struct cell*) {
    field mode: Mode;
    match mode {
        Mode::Held => {
            owns cell_value(cell);
            fact cell != 0;
        },
        Mode::Empty => {
            fact cell == 0;
        },
    }
}

verifying "resource_match_arm_unnamed_child.c";

void set(struct cell* cell) {
    owns m: maybe_cell(cell);
    requires m.mode == Mode::Held;
    ensures m.mode == Mode::Held;
} by {
    unfold(m);
    unfold(cell_value(cell));
    step();
    fold(cell_value(cell));
    let m = fold(maybe_cell(cell), { mode: Mode::Held });
    execute();
    simp();
}
```

```expect
pass
```
