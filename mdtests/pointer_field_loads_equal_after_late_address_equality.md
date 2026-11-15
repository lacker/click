# Field reads before an address equality

The reads of `pointer_loads_equal_after_late_address_equality.md`, at a field
eight bytes into each node. The numeric address of `a->next` is `address(a)`
plus the field's displacement, so the chain of C address equalities between
the node pointers relates the two field addresses, and the reads of one
state at them are equal.

```c filename=late_pointer_field_load_equality.c
struct node { int32 tag; struct node *next; };

int32 equal_reads(struct node *a, struct node *b, struct node *c,
                  struct node *d) {
    struct node *x = a->next;
    struct node *y = d->next;
    if (a != b) return 1;
    if (c != d) return 1;
    if (b != c) return 1;
    return x == y;
}
```

```click
verifying "late_pointer_field_load_equality.c";

int32 equal_reads(struct node* a, struct node* b, struct node* c,
                  struct node* d) {
    views a->next;
    views d->next;
    ensures result == 1;
} by {
    step();
    step();
    step();
    step();
    branch {
        step();
        solve();
    } else {}
    branch { step(); solve(); } else {}
    branch { step(); solve(); } else {}
    have x == y;
    step();
    solve();
}
```

```expect
pass
```
