# A field-bearing instance's published cells are read authority only

The companion refusal to
[`contract_owns_through_field_bearing_instance.md`](contract_owns_through_field_bearing_instance.md).
While a contract's clauses are evaluated, the folded `links: pair(node)`
publishes the cells its unmatched body owns so a sibling clause can load
`node->right`. That publication is a view: it makes the cell readable and
nothing more. Ownership of `node->right` stays inside the folded instance and
moves only on an explicit `unfold`.

`relink` stores to `node->right` without unfolding `links`. The sibling clause
`owns node->right->augmented` was addressable because the view let its base
load denote, but the store needs the cell owned, and the proof state holds it
only inside the folded instance, so the step is refused.

```c filename=relink.c
struct node {
    struct node *left;
    struct node *right;
    int32 augmented;
};

void relink(struct node *node) { node->right = 0; }
```

```click
resource pair(node: struct node*) {
    field weight: int32;
    owns &node->left;
    owns &node->right;
}

verifying "relink.c";

void relink(struct node* node) {
    requires node != 0;
    owns links: pair(node);
    owns node->right->augmented;
} by {
    execute();
}
```

```expect
fail: missing resource fact `owns node[2..3]`
```
