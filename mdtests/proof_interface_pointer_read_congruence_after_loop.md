# A post-loop interface retains pointer-read congruence

The loop gives the local pointers fresh names. Each arm proves the field read
through those aliases, but the interface checker may lower it with a different
read spelling. Both denote the same field in the same state.

```c filename=join-counted.c
struct node { unsigned long tag; struct node *other; struct node *next; };
void probe(struct node *p, struct node *q, struct node *value) { struct node *parent = p; struct node *successor = value; int n = 1; while (n > 0) { parent = p; successor = value; n = n - 1; } }
```

```click
verifying "join-counted.c";
spec enum Tag { Top, At(struct node*) }
resource link(p: struct node*, value: struct node*) {
    field model: Tag;
    match model {
        Tag::Top => { owns p->next; fact p->next == value; },
        Tag::At(id) => { owns id->other; owns id->next; fact p == id; fact id->next == value; },
    }
}
resource frame(p: struct node*) {
    field model: Tag;
    match model {
        Tag::Top => { },
        Tag::At(id) => { owns id->other; fact p == id; },
    }
}
void probe(struct node *p, struct node *q, struct node *value) {
    consumes a: link(p, value);
    produces p->next;
    produces b: frame(p);
    ensures p->next == value;
} by {
    step(); step(); step(); step(); step(); step();
    loop {
        decreases n;
        invariant n >= 0;
        owns a: link(p, value);
        invariant parent == p;
        invariant successor == value;
        initialize by close();
        maintain by { step(); step(); step(); }
    }
    match a.model ensuring {
        owns parent->next;
        owns b: frame(p);
        fact parent->next == successor;
    } {
        Tag::Top => {
            unfold(a);
            let b = fold(frame(p), {model: Tag::Top});
            have parent->next == successor;
        },
        Tag::At(id) => {
            unfold(a);
            have parent == id by close();
            have parent->next == id->next by {
                rewrite(parent, id);
                close();
            }
            have parent->next == successor;
            let b = fold(frame(p), {model: Tag::At(id)});
            have parent->next == successor;
        },
    }
    step_until(function.exit); close();
}
```

```expect
pass
```
