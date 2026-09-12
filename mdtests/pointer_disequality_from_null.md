# A pointer comparison decided by null-ness

A C test between two pointers is decided when the context already says one of
them is null and the other is not: if the offsets were the same the two
pointers would be one pointer, and one pointer cannot be both null and
non-null. The rule is two keyed lookups on the pointers in the test, so it
costs the same whether the context holds two facts or two thousand.

The second function reads the null side out of an owned cell rather than a
parameter. Nothing changes: the loaded value is a pointer like any other, and
the requirement files its null-ness under the loaded pointer's own offset.

```c filename=pointer_disequality_from_null.c
struct node {
    struct node *left;
    int32 value;
};

int32 parameter_is_null(struct node *p, struct node *q) {
    if (p == q)
        return 1;
    return 0;
}

int32 cell_is_null(struct node *n, struct node *q) {
    if (n->left == q)
        return 1;
    return 0;
}
```

```click
verifying "pointer_disequality_from_null.c";

int32 parameter_is_null(struct node* p, struct node* q) {
    requires p == 0;
    requires q != 0;
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 cell_is_null(struct node* n, struct node* q) {
    owns n->left;
    requires n->left == 0;
    requires q != 0;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
