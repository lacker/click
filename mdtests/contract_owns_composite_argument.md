# A folded composite supplies a dependent composite argument

The first `pair(node)` clause owns `node`'s cell and the first link-sized cell
of `node`'s left child.  The second clause must load `node->left->left` to form its
argument; its access comes from the whole entry clause set, including the
folded body of the first composite.  The clauses are intentionally written
in dependency order here and are checked by the same kernel evaluator used
for named contracts.

```c filename=dependent_pair.c
struct node {
    struct node *left;
    int32 value;
};

void probe(struct node *node) { }
```

```click
resource pair(node: struct node*) {
    owns node[0..1];
    owns node->left[0..1];
}

verifying "dependent_pair.c";

void probe(struct node* node) {
    requires node != 0;
    requires node->left != 0;
    views node[0..1];
    owns pair(node);
    owns pair(node->left->left);
    owns pair(node->left->left->left);
}

contract void DependentPair(struct node* node) {
    requires node != 0;
    requires node->left != 0;
    views node[0..1];
    owns pair(node);
    owns pair(node->left->left);
    owns pair(node->left->left->left);
}
```

```expect
pass
```
