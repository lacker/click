# A contract owns a segment whose base another clause supplies

`probe` owns `pair(node)`, which owns `node->left` and `node->right`, and then
owns `node->right->augmented`, whose base is loaded through `node->right` — a
cell the same contract already owns, from inside a folded composite.

A resource clause is evaluated against the loadability the whole clause set
supplies, the way a `requires` clause is, so the base load denotes and the
segment evaluates. The body then writes the segment, which is only possible if
the contract really transferred that cell; the proof opens `pair(node)` because
reading `node->right` at a step still needs the cell in hand, and closes it
again at the exit.

Clause order does not decide the contract: the same two clauses written the
other way round are the same contract, so `probe_reversed` states them in the
opposite order and carries the identical proof.

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
    owns node->left;
    owns node->right;
}

verifying "probe.c";

void probe(struct node* node) {
    requires node != 0;
    requires node->right != 0;
    owns pair(node);
    owns node->right->augmented;

    ensures node->right->augmented == 7;
} by {
    unfold(pair(node));
    execute();
    fold(pair(node));
    simp();
}

void probe_reversed(struct node* node) {
    requires node != 0;
    requires node->right != 0;
    owns node->right->augmented;
    owns pair(node);

    ensures node->right->augmented == 7;
} by {
    unfold(pair(node));
    execute();
    fold(pair(node));
    simp();
}
```

```expect
pass
```
