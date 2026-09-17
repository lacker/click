# A rotation helper calls an augmentation callback through a named contract

An augmented tree rotation takes the augmentation update as a callback, exactly
as Linux's `__rb_erase_color` takes `augment_rotate`. The helper rewires two
links, hands the old and new subtree roots to the callback, and returns the new
root. The callback is abstract: only the named contract `AugmentRotate`
justifies the indirect call.

The `augmented` cells stay outside the `shape` resource, so the callback can own
the two cells it updates while only viewing the tree the rotation rebuilt.
`bump` and `reset` form `AugmentRotate(&bump)` and `AugmentRotate(&reset)` at
the call site with no theorem.

The rotation helper consumes one folded `shape(node)` and owns the two
`augmented` cells beside it. `node->right->augmented` loads its base through
`node->right`, a cell that `shape(node)` owns, so this contract is exactly the
case where a resource clause reads a cell another clause of the same contract
supplies from inside a folded composite.

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

void bump(struct node *old, struct node *new) { new->augmented = old->augmented + 1; }
void reset(struct node *old, struct node *new) { old->augmented = 0; new->augmented = 0; }
void clobber(struct node *old, struct node *new) { new->augmented = 0; old->left = 0; }
void steal(struct node *old, struct node *new) { new->augmented = old->augmented; }

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
    requires 0 <= old->augmented;
    requires old->augmented < 1000;
    views shape(new);
    owns old->augmented;
    owns new->augmented;
    ensures 0 <= new->augmented;
    ensures new->augmented <= 1000;
}

void bump(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    requires old != new;
    requires 0 <= old->augmented;
    requires old->augmented < 1000;
    views shape(new);
    owns old->augmented;
    owns new->augmented;
    ensures 0 <= new->augmented;
    ensures new->augmented <= 1000;
} by {
    execute();
    simp();
}

void reset(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    requires old != new;
    views shape(new);
    owns old->augmented;
    owns new->augmented;
    ensures 0 <= new->augmented;
    ensures new->augmented <= 1000;
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
    requires 0 <= node->augmented;
    requires node->augmented < 1000;
    consumes shape(node);
    owns node->augmented;
    owns node->right->augmented;
    produces shape(result);

    ensures result == old(node->right);
    ensures 0 <= result->augmented;
    ensures result->augmented <= 1000;
} by {
    unfold(shape(node));
    unfold(shape(node->right));
    step();
    step();
    step();
    step();
    step();
    step();
    fold(shape(node));
    fold(shape(pivot));
    step();
    step();
    simp();
}

struct node* rotate_bump(struct node* node) {
    requires node != 0;
    requires node->right != 0;
    requires node != node->right;
    requires 0 <= node->augmented;
    requires node->augmented < 1000;
    consumes shape(node);
    owns node->augmented;
    owns node->right->augmented;
    produces shape(result);

    ensures result == old(node->right);
    ensures 0 <= result->augmented;
    ensures result->augmented <= 1000;
} by {
    execute();
    simp();
}

struct node* rotate_reset(struct node* node) {
    requires node != 0;
    requires node->right != 0;
    requires node != node->right;
    requires 0 <= node->augmented;
    requires node->augmented < 1000;
    consumes shape(node);
    owns node->augmented;
    owns node->right->augmented;
    produces shape(result);

    ensures result == old(node->right);
    ensures 0 <= result->augmented;
    ensures result->augmented <= 1000;
} by {
    execute();
    simp();
}
```

```expect
pass
```
