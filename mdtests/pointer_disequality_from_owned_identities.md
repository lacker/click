# Two owned nodes named by arm identities are different pointers

The cells of `a` and `b` are owned by two instances the proof opens one at a
time, and each instance owns its cell under the identity payload its arm
bound rather than under the parameter: `owns identity->value` with
`fact p == identity`. Neither the entry composition nor either opened body
holds both cells, and neither cell is filed under the pointer the C compares.

A pointer comparison composes its own two holders: the owned member holding
each compared address, found under the address itself or under a pointer an
exact equality proves it equal to, is assumed as a two-member composition for
that comparison, exactly as a store's opened composition is kept for the
store. Distinct owned members are separate, so the `if (a == b)` is decided
false before it splits, and the `step()` takes the one feasible arm.

```c filename=pointer_disequality_from_owned_identities.c
struct node {
    int32 value;
    struct node *next;
};

int32 same_node(struct node *a, struct node *b) {
    if (a == b)
        return 1;
    return 0;
}
```

```click
verifying "pointer_disequality_from_owned_identities.c";

spec enum Cell {
    Missing,
    Present(struct node*),
}

resource cell_at(p: struct node*) {
    field model: Cell;
    match model {
        Cell::Missing => { fact p == 0; },
        Cell::Present(identity) => {
            owns identity->value;
            fact p != 0;
            fact p == identity;
        },
    }
}

int32 same_node(struct node* a, struct node* b) {
    owns x: cell_at(a);
    owns y: cell_at(b);
    requires x.model != Cell::Missing;
    requires y.model != Cell::Missing;
    ensures result == 0;
} by {
    match x.model {
        Cell::Missing => { contradiction(x.model == Cell::Missing); },
        Cell::Present(xi) => {
            match y.model {
                Cell::Missing => { contradiction(y.model == Cell::Missing); },
                Cell::Present(yi) => {
                    unfold(x);
                    unfold(y);
                    step();
                    let x = fold(cell_at(a), { model: Cell::Present(xi) });
                    let y = fold(cell_at(b), { model: Cell::Present(yi) });
                    execute();
                    simp();
                },
            }
        },
    }
}
```

```expect
pass
```
