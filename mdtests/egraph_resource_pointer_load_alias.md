# Resource-published pointer loads through a proved-equal model identity

Unfolding owns one pointer cell and proves its parameter equal to the model
identity. No C read, write, recursive resource, or state transport is involved.
Address congruence must also give equality of the specification pointer loads.

```c filename=resource_pointer_load_alias.c
struct node { struct node *next; };
void check(struct node *p) {}
```

```click
verifying "resource_pointer_load_alias.c";

spec enum Cell { At(struct node*) }

resource cell(p: struct node*) {
    field model: Cell;
    match model {
        Cell::At(id) => {
            owns p->next;
            fact p != 0;
            fact p == id;
        },
    }
}

void check(struct node* p) {
    consumes c: cell(p);
} by {
    match c.model {
        Cell::At(id) => {
            unfold(c);
            have p == id;
            have &p->next == &id->next;
            have p->next == id->next;
            step_until(function.exit);
            close();
        },
    }
}
```

```expect
pass
```
