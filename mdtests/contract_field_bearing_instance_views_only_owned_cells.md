# A field-bearing instance publishes only the cells its body owns

The companion refusal to
[`contract_owns_through_field_bearing_instance.md`](contract_owns_through_field_bearing_instance.md).
A folded instance whose body is unconditional and unmatched publishes the
cells that body owns as read authority for its sibling clauses. Here `left`
owns `node->left` and not `node->right`, so the sibling clause
`owns node->right->augmented` has no authority to load its base and the
contract is refused before any proof runs. Publication is the body's own
footprint, not everything near it.

```c filename=probe.c
struct node {
    struct node *left;
    struct node *right;
    int32 augmented;
};

void probe(struct node *node) { node->right->augmented = 7; }
```

```click
resource left(node: struct node*) {
    field weight: int32;
    owns &node->left;
}

verifying "probe.c";

void probe(struct node* node) {
    requires node != 0;
    owns link: left(node);
    owns node->right->augmented;
} by {
    execute();
}
```

```expect
fail: could not address resource clause `node->right->augmented` (resource clause 2 of 2): missing pure fact: viewable(base=node[2], bytes=8)
```
