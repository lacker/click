# A contract whose resource clauses have no evaluable order is refused

A resource clause may read a cell any other clause of the same contract
supplies, so clause order does not decide a contract. What a clause may not do
is wait on a cell that no clause supplies before it — whether because two
clauses each wait on the other, or because the clause that would supply the
cell was never written.

`pair(node)` owns `node->left` and `node->right`, so both segments below get
their first link. Neither gets its second: `node->left->left` would come from
`pair(node->left)` and `node->right->right` from `pair(node->right)`, and the
contract declares neither. No order evaluates the two segments, so Click names
both positions rather than blaming whichever one happens to be written second.

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
    requires node->left != 0;
    requires node->right != 0;
    owns pair(node);
    owns node->left->left->augmented;
    owns node->right->right->augmented;
}
```

```expect
fail: resource clauses 2 and 3 cannot be evaluated in any order: each needs a cell no clause evaluated before it supplies
```
