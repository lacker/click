# A refused clause is numbered by the clause the contract wrote

`owns n->payload;` names an embedded struct array field, one clause that
lowers to one memory spec per element. The stalled `views n->next->augmented`
behind it is the second of two clauses the contract wrote, and that is how
the refusal names it: the kernel numbers a clause by the source position
carried on every spec it lowers to, not by counting specs, which would call
this clause the third of three.

```c filename=bump.c
struct pair {
    int32 first;
    int32 second;
};

struct node {
    struct pair payload[2];
    struct node *next;
    int32 augmented;
};

void bump(struct node *n) { n->augmented = n->next->augmented; }
```

```click
verifying "bump.c";

void bump(struct node* n) {
    requires n != 0;
    owns n->payload;
    views n->next->augmented;
} by {
    execute();
    simp();
}
```

```expect
fail: resource clause 2 of 2
```
