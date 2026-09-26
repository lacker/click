# A fold argument may name a proof arm's binding

A proof `match` arm binds a constructor's pointer payload, and every term the
arm writes may name it: `have` goals, theorem arguments, and a fold's model
fields. A fold's resource arguments are terms the arm writes too, so
`fold(cell_at(id), ...)` refolds the instance at the pointer the arm bound,
exactly as `fold(cell_at(p), ...)` does at the C parameter the arm's
`fact p == id` identifies it with. The resource arguments used to be lowered
as C expressions only, and the binding was refused as an unbound variable.

```c filename=fold_arm_binding.c
struct cell { unsigned long word; };

void stamp(struct cell *p) {
    p->word = 7;
}
```

```click
verifying "fold_arm_binding.c";

spec enum Cell { At(struct cell*) }

resource cell_at(p: struct cell*) {
    field model: Cell;
    match model {
        Cell::At(id) => {
            owns p->word;
            fact p == id;
        },
    }
}

void stamp(struct cell* p) {
    consumes c: cell_at(p);
    produces d: cell_at(p);
    ensures d.model == old(c.model);
} by {
    match c.model {
        Cell::At(id) => {
            unfold(c);
            step();
            let d = fold(cell_at(id), { model: Cell::At(id) });
            step();
            simp();
        },
    }
}
```

```expect
pass
```
