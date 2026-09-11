# Contract certification reports why the entry resources could not be built

`probe` owns `pair(node)`, which owns `node->left` and `node->right`, and then
owns `node->right->right->augmented`. Its base loads `node->right`, a cell the
contract does own through the folded `pair(node)`, and then
`node->right->right`, which nothing in the contract owns. No clause can supply
that second link, so the segment cannot be evaluated and the contract is
rejected.

The point of this fixture is the message, not the verdict: the runtime error
raised while evaluating the entry resource clauses has to reach the user
instead of being replaced by an empty path set. The case one link shallower is
`mdtests/contract_owns_through_composite_field.md`, where the clause set does
supply the base and the contract passes.

```c filename=probe.c
struct node {
    struct node *left;
    struct node *right;
    int32 augmented;
};

void probe(struct node *node) { }
```

```click
resource pair(node: struct node*) {
    owns node->left;
    owns node->right;
}

verifying "probe.c";

void probe(struct node* node) {
    requires node != 0;
    requires node->right != 0;
    owns pair(node);
    owns node->right->right->augmented;
}
```

```expect
fail: could not evaluate the contract entry resources: could not evaluate an owned memory resource segment (resource clause 2 of 2)
```
