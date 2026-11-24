# A loop invariant retains a child model through its folded parent

The child `c` is consumed by the fold of `w`. Match the held wrapper's
model before the loop and keep its payload in a proof binding. This is the
repair suggested by the neighbouring [refusal fixture](loop_invariant_old_model_of_an_instance_folded_into_a_parent.md); the C and contract are unchanged.

```c filename=count_down.c
struct node { int32 shade; };

int32 count_down(struct node* p, int32 n) {
    while (n > 0)
        n = n - 1;
    return 0;
}
```

```click
verifying "count_down.c";

spec enum Cell {
    Missing,
    Present(struct node*),
}

spec enum Wrap { Wrap(Cell) }

resource cell_at(p: struct node*) {
    field model: Cell;
    match model {
        Cell::Missing => { fact p == 0; },
        Cell::Present(identity) => {
            owns identity->shade;
            fact p != 0;
            fact p == identity;
        },
    }
}

resource wrap_at(p: struct node*) {
    field model: Wrap;
    match model {
        Wrap::Wrap(inner_model) => {
            owns inner: cell_at(p);
            fact inner.model == inner_model;
        },
    }
}

int32 count_down(struct node* p, int32 n) {
    requires n >= 0;
    consumes c: cell_at(p);
    produces w: wrap_at(p);
    ensures w.model == Wrap::Wrap(old(c.model));
} by {
    let w = fold(wrap_at(p), { model: Wrap::Wrap(old(c.model)), inner: c });
    match w.model {
        Wrap::Wrap(entry_model) => {
            have Wrap::Wrap(entry_model) == Wrap::Wrap(old(c.model)) by {
                rewrite(Wrap::Wrap(entry_model), w.model);
                rewrite(w.model, Wrap::Wrap(old(c.model)));
                close();
            }
            have entry_model == old(c.model) by close();
            loop {
                decreases n;
                owns w: wrap_at(p);
                invariant n >= 0;
                invariant w.model == Wrap::Wrap(entry_model);
            }
            step_until(function.exit);
            close();
        },
    }
}
```

```expect
pass
```
