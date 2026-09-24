# A contract owns a segment whose base a folded field-bearing instance supplies

The field-bearing twin of
[`contract_owns_through_composite_field.md`](contract_owns_through_composite_field.md).
`probe` owns `links: pair(node)`, an instance of a resource that carries a
plain field `weight` beside the cells `node->left` and `node->right`, and then
owns `node->right->augmented`, whose base is loaded through `node->right`.

The body of `pair` is unconditional and unmatched, so while the contract's
clauses are evaluated the folded instance publishes the cells it owns as read
authority for the sibling clauses, exactly as a folded field-free composite
and a decided match arm do. The base load denotes and the segment evaluates.
The instance stays folded: the body writes the segment, which is only possible
if the contract really transferred that cell, and the proof opens `links`
explicitly because a C read of `node->right` at a step still needs the cell in
hand, then refolds it at the weight it held.

Clause order does not decide the contract: `probe_reversed` states the two
clauses the other way round and carries the identical proof.

```c filename=probe.c
struct node {
    struct node *left;
    struct node *right;
    int32 augmented;
};

void probe(struct node *node) { node->right->augmented = 7; }

void probe_reversed(struct node *node) { node->right->augmented = 7; }
```

```click
resource pair(node: struct node*) {
    field weight: int32;
    owns &node->left;
    owns &node->right;
}

verifying "probe.c";

void probe(struct node* node) {
    requires node != 0;
    owns links: pair(node);
    owns node->right->augmented;

    ensures links.weight == old(links.weight);
    ensures node->right->augmented == 7;
} by {
    let { weight: w } = unfold(links);
    execute();
    let links = fold(pair(node), { weight: w });
    simp();
}

void probe_reversed(struct node* node) {
    requires node != 0;
    owns node->right->augmented;
    owns links: pair(node);

    ensures links.weight == old(links.weight);
    ensures node->right->augmented == 7;
} by {
    let { weight: w } = unfold(links);
    execute();
    let links = fold(pair(node), { weight: w });
    simp();
}
```

```expect
pass
```
