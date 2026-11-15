# Rewrite an alias in a viewability claim

A resource model can name a pointer differently from the C argument that owns
its bytes. An exact pointer equality lets `rewrite` change the base of an
explicit `viewable` goal. It preserves the memory state and byte extent;
the existing ownership still supplies the required authority.

```c filename=alias.c
struct cell { int32 value; };
void keep(struct cell *c) {}
```

```click
verifying "alias.c";

spec enum Link { Node(struct cell*) }
resource Cell(p: struct cell*) {
    field model: Link;
    match model {
        Link::Node(q) => { owns p[0..1]; fact p == q; },
    }
}

void keep(struct cell* c) {
    owns h: Cell(c);
} by {
    match h.model {
        Link::Node(q) => {
            unfold(h);
            have viewable(q[0..1]) by {
                rewrite(q, c);
                known();
            }
            let h = fold(Cell(c), { model: Link::Node(q) });
            step_until(function.exit);
            solve();
        },
    }
}
```

```expect
pass
```
