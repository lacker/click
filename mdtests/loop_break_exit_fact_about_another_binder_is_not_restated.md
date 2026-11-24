# A fact about another binder is not restated about the renamed one

`inspect` holds two instances. Every `break` exit refolds `x` at a different
constructor, so the join gives `x`'s model a fresh name. No exit touches `y`,
and every exit states `y.model == old(y.model)`, which survives the join as
it always did, because every exit states that very fact.

Restating replaces an exit's value for the renamed binder, and only that. The
fact about `y` does not mention `x`'s value at any exit, so nothing is
restated about `x`, and the claim `x.model == old(y.model)` is refused. See
[`loop_break_exit_keeps_a_fact_every_exit_restates.md`](loop_break_exit_keeps_a_fact_every_exit_restates.md)
for the rule.

```c filename=two_cells.c
struct node { int32 shade; };

int32 inspect(struct node* p, struct node* q) {
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
verifying "two_cells.c";

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

int32 inspect(struct node* p, struct node* q) {
    owns x: cell_at(p);
    owns y: cell_at(q);
    ensures result == 0;
    ensures x.model == old(y.model);
} by {
    step();
    step();
    loop {
        decreases 0;
        owns x: cell_at(p);
        owns y: cell_at(q);
        invariant y.model == old(y.model);

        maintain by {
            match x.model {
                Cell::Missing => {
                    unfold(x);
                    let x = fold(cell_at(p), { model: Cell::Missing });
                    step();
                    step();
                },
                Cell::Red(identity) => {
                    unfold(x);
                    step();
                    step();
                    step();
                    let x = fold(cell_at(p), { model: Cell::Red(identity) });
                    step();
                },
                Cell::Black(identity) => {
                    unfold(x);
                    step();
                    step();
                    step();
                    let x = fold(cell_at(p), { model: Cell::Black(identity) });
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
fail: `ensures x.model == old(y.model)` failed
```
