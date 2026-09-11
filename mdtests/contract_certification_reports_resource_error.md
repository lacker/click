# A contract names the resource clause it could not address

`probe` owns `pair(node)`, which owns `node->left` and `node->right`, and then
owns `node->right->right->augmented`. Its base loads `node->right`, a cell the
contract does own through the folded `pair(node)`, and then
`node->right->right`, which nothing in the contract owns. No clause can supply
that second link, so the clause cannot be addressed and the contract is
rejected.

The point of this fixture is the message, not the verdict: the user gets the
clause that stalled, spelled as it was written, and the cell it wanted, instead
of an empty path set. The contract is refused where it is addressed, which is
ahead of certification, so the message reads as the addressing failure it is
rather than as a runtime error inside the kernel's section evaluator; both
name the clause by the same position. The case one link shallower is
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
fail: could not address resource clause `node->right->right->augmented` (resource clause 2 of 2): missing pure fact: loadable(
```
