# A call retains its abstract resource bound without unfolding recursive cells

```c filename=footprint.c
struct node { struct node *next; };
void touch(struct node *child, struct node *other) {}
void caller(struct node *child, struct node *other, int *slot) { touch(child, other); }
```

```click
import click::separation;
verifying "footprint.c";
resource list(p: struct node*) {
    if p != 0 {
        owns p->next;
        owns list(p->next);
    }
}
void touch(struct node* child, struct node* other) { owns list(child); owns list(other); }
void caller(struct node* child, struct node* other, int32* slot) {
    owns list(child);
    owns list(other);
    owns *slot;
} by {
    have separate(list(child), memory(*slot)) by { close(); }
    have separate(list(other), memory(*slot)) by { close(); }
    apply(separation::separate_star(list(child), list(other), memory(*slot)));
    mark before_call;
    step();
    have contains(list(child), statement(0).footprint) by { close(); }
}
```

```expect
fail: could not establish `contains(list(child), statement(0).footprint)`
```
