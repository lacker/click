# Seeded pointer fields retain their read identity through model aliases

The field is at byte offset 16. The entry resource already names its pointer
value before any C load occurs. A model match gives another name for its base;
both logical field reads must name the same value in the same state.

```c filename=probe.c
struct node { unsigned long tag; struct node *other; struct node *next; };
void probe(struct node *p, struct node *q, struct node *value) {}
```

```click
verifying "probe.c";
spec enum Tag { At(struct node*) }
resource alias(p: struct node*) {
    field model: Tag;
    match model {
        Tag::At(id) => { owns id->other; fact p == id; },
    }
}
void probe(struct node *p, struct node *q, struct node *value) {
    owns p->next;
    consumes a: alias(p);
    requires p->next == value;
    produces b: alias(p);
    ensures p->next == value;
} by {
    match a.model {
        Tag::At(id) => {
            unfold(a);
            have p == id;
            have &p->next == &id->next;
            have p->next == id->next;
            have id->next == value;
            let b = fold(alias(p), { model: Tag::At(id) });
            step_until(function.exit); solve();
        },
    }
}
```

```expect
pass
```
