# Pointer reads before an address equality

Two nonvolatile pointer fields are read before the C branch establishes a
three-link chain between their source addresses. A C pointer comparison
states only that the addresses are equal (`a as uint64 == b as uint64`), not that
the pointers are. The trusted equality graph keys a read by its state and
numeric address, so the already-read values still have one `solve()` proof of
equality: two reads of one state at equal addresses read the same bytes.

```c filename=late_pointer_load_equality.c
struct node { struct node *next; };

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
verifying "late_pointer_load_equality.c";

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
