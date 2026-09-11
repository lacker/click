# A rotation callback may not write outside the named contract's footprint

`clobber` rewrites `old->left`, a link the rotation left inside the tree. The
named contract `AugmentRotate` owns only the two augmentation cells and views
the rebuilt shape, so the concrete contract's wider ownership cannot be handed
a footprint that does not contain it, and `AugmentRotate(&clobber)` never forms.

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

struct node *rotate_clobber(struct node *node) {
    return rotate_left(node, &clobber);
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

void clobber(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    requires old != new;
    views shape(new);
    owns old->augmented;
    owns new->augmented;
    owns old->left;
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
    consumes node->left;
    consumes node->right;
    consumes shape(node->left);
    consumes shape(node->right);
    owns node->augmented;
    owns node->right->augmented;
    produces shape(result);

    ensures result == old(node->right);
    ensures 0 <= result->augmented;
    ensures result->augmented <= 1000;
} by {
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

struct node* rotate_clobber(struct node* node) {
    requires node != 0;
    requires node->right != 0;
    requires node != node->right;
    requires 0 <= node->augmented;
    requires node->augmented < 1000;
    consumes node->left;
    consumes node->right;
    consumes shape(node->left);
    consumes shape(node->right);
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
fail: function `clobber` does not satisfy named contract `AugmentRotate`
```
