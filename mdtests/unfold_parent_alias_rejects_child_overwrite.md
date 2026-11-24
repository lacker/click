# A parent alias cannot preserve an overwritten child pointer

A store replaces the parent pointer field after the call. Its old folded
child must not satisfy the new pointer argument.

```c filename=probe.c
struct node { unsigned long tag; struct node *other; struct node *next; };
void helper(struct node *q) { q->tag = 0; }
void probe(struct node *p, struct node *q) { helper(q); p->other = q; }
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
    owns q->tag;
    consumes a: frame(p);
    produces b: frame(p);
    ensures b.model == old(a.model);
} by {
    match a.model {
        Tag::At(id, cm) => {
            let {kid: kid} = unfold(a);
            have p == id by close();
            step(); step();
            let b = fold(frame(p), { model: Tag::At(id, cm), kid: kid });
        },
    }
}
```

```expect
fail: child `kid` is not proven to have the arguments the parent body gives it
```
