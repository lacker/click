# A caller keeps aliased field ownership across a call

The field belongs to an unfolded modeled node. The call frame must find the
kept field through the checked parent alias and cover the full pointer width.
No explicit separation from the helper's tag is supplied.

The final store proves the field equals `q`. The following check asks for
the earlier value and must refuse.

```c filename=probe.c
struct node { unsigned long tag; struct node *other; struct node *next; };
void helper(struct node *q) { q->tag = 0; }
void probe(struct node *p, struct node *q) { q->next = p; helper(q); p->other = q; }
```

```click
verifying "probe.c";
spec enum Tag { At(struct node*, Child) }
spec enum Child { Empty }
resource child(p: struct node*) { field model: Child; owns p->tag; }
resource frame(p: struct node*) {
    field model: Tag;
    match model {
        Tag::At(id, cm) => {
            owns id->other;
            owns kid: child(id->other);
            fact kid.model == cm;
            fact p == id;
        },
    }
}
void helper(struct node *q) { owns q->tag; }
void probe(struct node *p, struct node *q) {
    owns q->tag; owns q->next; owns q->other;
    consumes a: frame(p);
    requires separate(memory(p->other), memory(q->next));
    requires separate(memory(p->other), memory(q->other));
} by {
    match a.model {
        Tag::At(id, cm) => {
            let {kid: kid} = unfold(a);
            have p == id by close();
            step(); mark before; step(); step();
            have p->other == q by close();
            have p->other == at(before, p->other) by close();
        },
    }
}
```

```expect
fail: `have` failed for `p->other == at(before, p->other)`
```
