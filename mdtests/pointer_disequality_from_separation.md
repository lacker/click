# A pointer comparison decided by separate ownership

Two objects owned at once are separate, and two non-empty ranges at the same
base overlap. So the bases of two separately owned objects are different
pointers, and a C test between them is decided before it splits.

The separation needs no `have`: the composition of the two `owns` clauses
projects the same-block pair, and the pair is indexed by the two base offsets
the comparison itself names. The negative, one object owned, is in
[`pointer_disequality_rejects_undecided.md`](pointer_disequality_rejects_undecided.md).

```c filename=pointer_disequality_from_separation.c
struct node {
    struct node *left;
    int32 value;
};

int32 both_owned(struct node *a, struct node *b) {
    if (a == b)
        return 1;
    return 0;
}
```

```click
verifying "pointer_disequality_from_separation.c";

int32 both_owned(struct node* a, struct node* b) {
    owns a->left;
    owns b->left;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
