# Unfolded scalar facts do not survive a write through their C alias

The frame initially states an odd tag word. A C write clears it through the
parameter proven equal to the model pointer; the old scalar fact must not
justify a claim about the new state.

```c filename=probe.c
struct node { unsigned long tag; struct node *other; struct node *next; };
void probe(struct node *p) { p->tag = 0; }
```

```click
verifying "probe.c";
spec enum Child { Empty }
spec enum Tag { At(struct node*, struct node*, Child) }
resource child(p: struct node*) {
    field model: Child;
    owns p->tag;
    fact p != 0;
}
resource frame(p: struct node*) {
    field model: Tag;
    match model {
        Tag::At(id, gp, child_model) => {
            owns id->tag;
            owns id->other;
            owns kid: child(id->other);
            fact kid.model == child_model;
            fact p == id;
            fact id != 0;
            fact aligned(id, 8);
            fact aligned(gp, 8);
            fact id->tag == address(gp) + (id->tag & 1);
            fact (id->tag & 1) == 1;
        },
    }
}
void probe(struct node *p) {
    consumes a: frame(p);
    produces b: frame(p);
    ensures b.model == old(a.model);
} by {
    match a.model {
        Tag::At(id, gp, child_model) => {
            let {kid: kid} = unfold(a);
            step_until(function.exit);
            have (id->tag & 1) == 1 by known();
            have p != 0 by { rewrite(p, id); known(); }
            have aligned(p, 8) by { rewrite(p, id); known(); }
            let b = fold(frame(p), { model: Tag::At(id, gp, child_model), kid: kid });
            solve();
        },
    }
}
```

```expect
fail: `known()` could not close the current goal
```
