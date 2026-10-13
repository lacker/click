# A field-bearing instance publishes only the cells its body owns

A companion refusal to
[`contract_returns_field_bearing_sibling.md`](contract_returns_field_bearing_sibling.md),
where a folded field-bearing instance's published cells let a sibling clause
load its argument.
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
    owns node->left;
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
fail: could not address resource clause `node->right->augmented` (resource clause 2 of 2): missing pure fact: viewable(((uint8 *)&node->right)[0..8])
```
