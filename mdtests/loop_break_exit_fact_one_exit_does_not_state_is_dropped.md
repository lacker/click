# A loop join cannot preserve a model that one break exit changes

Two exits preserve the entry model, while the `Cell::Black` exit deliberately
refolds its resource with `Cell::Red`. Both variants permit the same owned cell,
so the refold is valid, but the model-equality postcondition is false on that
exit. The join must not borrow the equality from its other two exits.

A missing explicit `have` alone is insufficient for a negative test: when all
exits refold the same model, checked constructor equalities can establish the
postcondition through equality closure.

```c filename=one_cell_one_silent_exit.c
struct node { int32 shade; };

int32 inspect(struct node* p) {
    int32 seen = 0;
    while (true) {
        if (p == 0)
            break;
        seen = p->shade;
        break;
    }
    return 0;
}
```

```click
verifying "one_cell_one_silent_exit.c";

spec enum Cell {
    Missing,
    Red(struct node*),
    Black(struct node*),
}

resource cell_at(p: struct node*) {
    field model: Cell;
    match model {
        Cell::Missing => { fact p == 0; },
        Cell::Red(identity) => {
            owns identity->shade;
            fact p != 0;
            fact p == identity;
        },
        Cell::Black(identity) => {
            owns identity->shade;
            fact p != 0;
            fact p == identity;
        },
    }
}

int32 inspect(struct node* p) {
    owns x: cell_at(p);
    ensures result == 0;
    ensures x.model == old(x.model);
} by {
    step();
    step();
    loop {
        decreases 0;
        owns x: cell_at(p);
        invariant x.model == old(x.model);

        maintain by {
            match x.model {
                Cell::Missing => {
                    have Cell::Missing == old(x.model) by {
                        rewrite(Cell::Missing, x.model);
                        close();
                    }
                    unfold(x);
                    let x = fold(cell_at(p), { model: Cell::Missing });
                    have x.model == old(x.model) by {
                        rewrite(x.model, Cell::Missing);
                        close();
                    }
                    step();
                    step();
                },
                Cell::Red(identity) => {
                    have Cell::Red(identity) == old(x.model) by {
                        rewrite(Cell::Red(identity), x.model);
                        close();
                    }
                    unfold(x);
                    step();
                    step();
                    step();
                    let x = fold(cell_at(p), { model: Cell::Red(identity) });
                    have x.model == old(x.model) by {
                        rewrite(x.model, Cell::Red(identity));
                        close();
                    }
                    step();
                },
                Cell::Black(identity) => {
                    unfold(x);
                    step();
                    step();
                    step();
                    let x = fold(cell_at(p), { model: Cell::Red(identity) });
                    step();
                },
            }
        }
    }
    step();
    close();
}
```

```expect
fail: `ensures x.model == old(x.model)` failed
```
