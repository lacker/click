# A dependent composite argument still needs access

Allowing entry lowering to retain a symbolic argument does not manufacture
the cell it reads.  With no precondition or resource clause supplying
`node->left`, the authoritative kernel evaluator rejects the composite
argument and identifies its source clause.

```c filename=dependent_pair_missing_access.c
struct node {
    struct node *left;
    int32 value;
};

void probe(struct node *node) { }
```

```click
resource pair(node: struct node*) {
    owns node->left[0..1];
}

verifying "dependent_pair_missing_access.c";

contract void DependentPair(struct node* node) {
    requires node != 0;
    owns pair(node->left->left);
}
```

```expect
fail: could not evaluate the contract entry resources: FunctionContract("could not evaluate resource `pair` argument 0
```
