# A rotation callback reads its argument's child augmentation

A realistic augmentation callback recomputes from the subtree it is handed,
so it reads a child cell through one of its own parameters. `bump` copies
`old->left->augmented` into `new->augmented`, which the callback contract
states as a guarded read: `requires old->left != 0` names the link,
`views old->left` holds the link cell the read goes through, and
`views old->left->augmented` holds the cell it lands on.

The contract is prepared in the entry state its own clauses build, so the
requirement and the resource clause that read `old->left` are justified by
the same fact. `reset` does not read the child at all; its weaker contract
still refines `AugmentRotate`, and both `AugmentRotate(&bump)` and
`AugmentRotate(&reset)` form at their call sites with no theorem.

The rotation folds the two subtree shapes after the callback rather than
before it, because the callback is handed the old root's link cells
directly instead of a view of the rebuilt shape.

```c filename=augment_rotate.c
struct node {
    struct node *left;
    struct node *right;
    int32 augmented;
};

struct node *rotate_left(struct node *node,
                         void (*augment_rotate)(struct node *old, struct node *new)) {
    struct node *pivot = node->right;
    struct node *middle = pivot->left;
    node->right = middle;
    pivot->left = node;
    augment_rotate(node, pivot);
    return pivot;
}

void bump(struct node *old, struct node *new) { new->augmented = old->left->augmented; }
void reset(struct node *old, struct node *new) { old->augmented = 0; new->augmented = 0; }

struct node *rotate_bump(struct node *node) {
    return rotate_left(node, &bump);
}

struct node *rotate_reset(struct node *node) {
    return rotate_left(node, &reset);
}
```

```click
resource shape(node: struct node*) {
    if node != 0 {
        owns node->left;
        owns node->right;
        contains shape(node->left);
        contains shape(node->right);
    }
}

verifying "augment_rotate.c";

contract void AugmentRotate(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    requires old != new;
    requires old->left != 0;
    views old->left->augmented;
    views old->left;
    owns old->augmented;
    owns new->augmented;
}

void bump(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    requires old != new;
    requires old->left != 0;
    views old->left->augmented;
    views old->left;
    owns old->augmented;
    owns new->augmented;
} by {
    execute();
    simp();
}

void reset(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    requires old != new;
    owns old->augmented;
    owns new->augmented;
} by {
    execute();
    simp();
}

struct node* rotate_left(
    struct node* node,
    void (*augment_rotate)(struct node*, struct node*)
) {
    requires AugmentRotate(augment_rotate);
    requires node != 0;
    requires node->right != 0;
    requires node != node->right;
    requires node->left != 0;
    consumes node->left;
    consumes node->right;
    consumes shape(node->left);
    consumes shape(node->right);
    views node->left->augmented;
    owns node->augmented;
    owns node->right->augmented;
    produces shape(result);

    ensures result == old(node->right);
} by {
    unfold(shape(node->right));
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    fold(shape(node));
    fold(shape(pivot));
    step();
    simp();
}

struct node* rotate_bump(struct node* node) {
    requires node != 0;
    requires node->right != 0;
    requires node != node->right;
    requires node->left != 0;
    consumes node->left;
    consumes node->right;
    consumes shape(node->left);
    consumes shape(node->right);
    views node->left->augmented;
    owns node->augmented;
    owns node->right->augmented;
    produces shape(result);

    ensures result == old(node->right);
} by {
    execute();
    simp();
}

struct node* rotate_reset(struct node* node) {
    requires node != 0;
    requires node->right != 0;
    requires node != node->right;
    requires node->left != 0;
    consumes node->left;
    consumes node->right;
    consumes shape(node->left);
    consumes shape(node->right);
    views node->left->augmented;
    owns node->augmented;
    owns node->right->augmented;
    produces shape(result);

    ensures result == old(node->right);
} by {
    execute();
    simp();
}
```

```expect
pass
```
