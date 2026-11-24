# A nested constructor-arm contradiction names its own source

```c filename=peek.c
struct node { int32 shade; };

int32 peek(struct node* p) {
    return 0;
}
```

```click
verifying "peek.c";

spec enum Cell {
    Missing,
    Present(struct node*),
}

resource cell_at(p: struct node*) {
    field model: Cell;
    match model {
        Cell::Missing => { },
        Cell::Present(identity) => {
            owns identity->shade;
            fact p == identity;
        },
    }
}

int32 peek(struct node* p) {
    owns x: cell_at(p);
    ensures result == 0;
} by {
    have p == p by normalize();
    match x.model {
        Cell::Missing => {
            step_until(function.exit);
            close();
        },
        Cell::Present(identity) => {
            match x.model {
                Cell::Missing => { step_until(function.exit); close(); },
                Cell::Present(child) => {
                    contradiction(x.model == Cell::Present(child));
                },
            }
        },
    }
}
```

```expect
fail: contradiction(x.model == Cell::Present(child))
```
