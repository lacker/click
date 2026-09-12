# A model's pointer payload is comparable with a C pointer

A modeled data structure carries node identity as a pointer payload, and the
resource that owns the node states `fact p == identity` in the matching arm.
That fact is the only bridge between the address the C compares and the
identity the model records, so a proposition has to be able to mention both.

This is the smallest shape of that bridge: one cell, a `Present` arm whose
first payload is the cell's own address, and a C function that answers whether
its second argument is that cell.

The proof uses the payload binding `identity` in four places a written
proposition can appear:

- `have p == identity`, a proposition mixing a C parameter with an arm
  binding, lowered against C state on one path;
- `rewrite(identity == p)`, which replaces the payload with the C pointer
  inside a goal, leaving a same-block pointer equality the listed premise
  `p == q` closes;
- `normalize() using { identity == q; }` inside a nested `branch` arm, where
  the arm bindings are still in scope; and
- the postcondition `result == cell_member(old(c.model), q)`, where
  `cell_member` compares the payload with a C pointer inside a pure function.

Pointers stay pointers throughout: nothing converts an address to an integer,
and the payload carries no ownership of its own.

```c filename=pointer_payload.c
struct cell {
    int value;
};

int cell_same(struct cell *p, struct cell *q) {
    if (p == q) {
        return 1;
    }
    return 0;
}
```

```click
verifying "pointer_payload.c";

spec enum CellModel {
    Missing,
    Present(struct cell*, int),
}

resource cell_at(p: struct cell*) {
    field model: CellModel;
    match model {
        CellModel::Missing => { fact p == 0; },
        CellModel::Present(identity, value) => {
            owns p->value;
            fact p != 0;
            fact p == identity;
            fact p->value == value;
        },
    }
}

function cell_member(cell: CellModel, target: struct cell*) -> int32 {
    match cell {
        CellModel::Missing => 0,
        CellModel::Present(identity, value) =>
            if identity == target { 1 } else { 0 },
    }
}

int cell_same(struct cell* p, struct cell* q) {
    owns c: cell_at(p);
    requires c.model != CellModel::Missing;
    ensures c.model == old(c.model);
    ensures result == cell_member(old(c.model), q);
} by {
    match c.model {
        CellModel::Missing => { contradiction(c.model == CellModel::Missing); },
        CellModel::Present(identity, value) => {
            unfold(c);
            have p == identity by { simp(); }
            have p->value == value by { simp(); }
            branch {
                then {
                    step();
                    let c = fold(cell_at(p), { model: old(c.model) });
                    have identity == q by { rewrite(identity == p); normalize() using { p == q; } }
                    have result == cell_member(old(c.model), q) by {
                        rewrite(old(c.model) == CellModel::Present(identity, value));
                        unfold(cell_member(CellModel::Present(identity, value), q));
                        normalize() using { identity == q; }
                    }
                    simp();
                }
                else {}
            }
            step();
            let c = fold(cell_at(p), { model: old(c.model) });
            have not(identity == q) by { rewrite(identity == p); normalize() using { not(p == q); } }
            have result == cell_member(old(c.model), q) by {
                rewrite(old(c.model) == CellModel::Present(identity, value));
                unfold(cell_member(CellModel::Present(identity, value), q));
                normalize() using { not(identity == q); }
            }
            simp();
        },
    }
}
```

```expect
pass
```

The same bridge, at the same `fact p == identity`, is what
`examples/modeled-binary-tree` uses to connect the C test `root == target` to
the model's identity payload.
